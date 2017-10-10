(ns parsers.core
  (:require [clojure.string :as string]
            [clojure.pprint :refer [pprint]]
            [clojure.set :as sets]
            [clojure.string :as strings]
            [schema.core :as s])
  (:import (cz.jirutka.rsql.parser.ast RSQLOperators ComparisonOperator AndNode OrNode ComparisonNode)
           (cz.jirutka.rsql.parser RSQLParser)
           (java.time.format DateTimeFormatter)
           (java.time Instant)
           (java.util Date)
           (org.bson.types ObjectId)))


;;; argument conversion

(derive ::or ::logical)
(derive ::and ::logical)
(derive ::== ::comparison)
(derive ::!= ::comparison)
(derive ::=q= ::comparison)
(derive ::=gt= ::comparison)
(derive ::=ge= ::comparison)
(derive ::=lt= ::comparison)
(derive ::=le= ::comparison)
(derive ::=re= ::comparison)
(derive ::=ex= ::comparison)
(derive ::=in= ::comparison)
(derive ::=out= ::comparison)

(defn get-namespace []
  (namespace ::_))

(defn keify [k]
  (keyword (get-namespace) (name k)))

(defn make-operator [op]
  (ComparisonOperator. (into-array String [op])))

(defn get-operators []
  (conj (into #{} (RSQLOperators/defaultOperators))
    (make-operator "=ex=")
    (make-operator "=re=")
    (make-operator "=q=")))

(defrecord Logical [op children]
  Object
  (toString [this]
    (with-out-str (pprint this))))

(defrecord Comparison [op hint path arguments]
  Object
  (toString [this]
    (with-out-str (pprint this))))

(declare parse parse-to-tree coerce-argument-types)

(defn has-type-hint? [n]
  (some? (get n :hint)))

(defn has-schema? [context node]
  (some? (get-in (get context :schema) (:path node))))

(defn trim-from-end [s end]
  (if (string/includes? s end)
    (.substring s 0 (.lastIndexOf s end))
    s))

(defn get-type-hint [s]
  (when (string/includes? s ":")
    (let [hint (keify (.substring s (inc (.lastIndexOf s ":"))))]
      (some #{::string ::boolean ::number ::date} [hint]))))

(defn get-selector-path [s]
  (mapv keyword (string/split (trim-from-end s ":") #"\.")))

(defmulti node->data class)

(defmethod node->data AndNode [node]
  (->Logical ::and (mapv node->data (.getChildren node))))

(defmethod node->data OrNode [node]
  (->Logical ::or (mapv node->data (.getChildren node))))

(defmethod node->data ComparisonNode [node]
  (map->Comparison
    {:op        (keify (.getSymbol (.getOperator node)))
     :hint      (get-type-hint (.getSelector node))
     :path      (get-selector-path (.getSelector node))
     :arguments (into [] (.getArguments node))}))

(defn coerce-node [f node]
  (update node :arguments (partial mapv f)))

(defn coerce-string [s] s)

(defn coerce-boolean [s]
  (case s "true" true "false" false))

(defn coerce-number [s]
  (try
    (Long/parseLong s)
    (catch Exception e
      (Double/parseDouble s))))

(defn coerce-date [s]
  (let [parser (DateTimeFormatter/ISO_DATE_TIME)]
    (Instant/from (.parse parser s))))

(defn coerce-object-id [^String s]
  (if (and (string? s) (ObjectId/isValid s)) (ObjectId. s) s))

(defn best-effort [s]
  (letfn [(attempt [s queue]
            (try ((first queue) s)
                 (catch Exception _
                   (attempt s (rest queue)))))]
    (attempt s [coerce-date coerce-number coerce-boolean coerce-string])))

(defn coercer [schema]
  (cond
    (identical? s/Str schema) coerce-string
    (identical? s/Int schema) coerce-number
    (identical? s/Inst schema) coerce-date
    (identical? s/Bool schema) coerce-boolean
    (identical? s/Num schema) coerce-number
    (.isAssignableFrom ObjectId schema) coerce-object-id
    (.isAssignableFrom String schema) coerce-string
    (.isAssignableFrom Number schema) coerce-number
    (.isAssignableFrom Boolean schema) coerce-boolean
    (.isAssignableFrom Date schema) coerce-date
    (.isAssignableFrom Instant schema) coerce-date))

(defn coerce-guess [n]
  (coerce-node best-effort n))

(defn coerce-schema [schema n]
  (coerce-node (coercer schema) n))

(defn coerce-hint [n]
  (case (:hint n)
    ::string (coerce-node coerce-string n)
    ::boolean (coerce-node coerce-boolean n)
    ::number (coerce-node coerce-number n)
    ::date (coerce-node coerce-date n)))

(defmulti visit-coercion
  (fn [_ {op :op}] (keyword op)))

(defmethod visit-coercion ::logical [context node]
  (update node :children (partial mapv (partial visit-coercion context))))

(defmethod visit-coercion ::=re= [_ n]
  (coerce-node coerce-string n))

(defmethod visit-coercion ::=ex= [_ n]
  (coerce-node coerce-boolean n))

(defmethod visit-coercion ::=q= [context n]
  (let [nested-context (update context :schema #(get-in % (:path n)))]
    (coerce-node (fn [arg] (visit-coercion nested-context (parse-to-tree arg))) n)))

(defmethod visit-coercion ::comparison [context n]
  (cond
    (has-type-hint? n) (coerce-hint n)
    (has-schema? context n) (coerce-schema (get-in (get context :schema) (:path n)) n)
    :else (coerce-guess n)))

(defn coerce-argument-types
  ([tree] (coerce-argument-types tree {}))
  ([tree schema] (visit-coercion {:schema schema} tree)))

(defn parse-to-tree [s]
  (-> (get-operators) (RSQLParser.) (.parse s) (node->data)))

(defn parse
  ([s] (parse s {}))
  ([s schema] (-> (parse-to-tree s) (coerce-argument-types schema))))


;;; predicates

(defn coll-like? [x]
  (and (not (string? x))
    (try (seq x) (catch Exception _))))

(defn coerce-to-set [x]
  (if (coll-like? x) (set x) #{x}))

(defn in [& args]
  (boolean
    (not-empty
      (apply sets/intersection
        (map coerce-to-set args)))))

(defn nin [& args]
  (boolean
    (empty?
      (apply sets/intersection
        (map coerce-to-set args)))))

(defn compare-coll [op & args]
  (apply op
    (if (every? coll-like? args)
      (map count args)
      (map first args))))

(defn gt [& args]
  (compare-coll > args))

(defn lt [& args]
  (compare-coll < args))

(defn gte [& args]
  (compare-coll >= args))

(defn lte [& args]
  (compare-coll <= args))

(defn mongo-path [node]
  (strings/join "." (map name (:path node))))

(defmulti visit-mongo
  (fn [_ {op :op}] op))

(defmethod visit-mongo ::or [context node]
  {"$or" (mapv (partial visit-mongo context) (:children node))})

(defmethod visit-mongo ::and [context node]
  {"$and" (mapv (partial visit-mongo context) (:children node))})

(defmethod visit-mongo ::== [context node]
  {(mongo-path node) (first (:arguments node))})

(defmethod visit-mongo ::!= [context node]
  {(mongo-path node) {"$ne" (first (:arguments node))}})

(defmethod visit-mongo ::=re= [context node]
  {(mongo-path node) {"$regex" (first (:arguments node))}})

(defmethod visit-mongo ::=in= [context node]
  {(mongo-path node) {"$in" (:arguments node [])}})

(defmethod visit-mongo ::=out= [context node]
  {(mongo-path node) {"$nin" (:arguments node [])}})

(defmethod visit-mongo ::=gt= [context node]
  {(mongo-path node) {"$gt" (first (:arguments node []))}})

(defmethod visit-mongo ::=lt= [context node]
  {(mongo-path node) {"$lt" (first (:arguments node []))}})

(defmethod visit-mongo ::=gte= [context node]
  {(mongo-path node) {"$gte" (first (:arguments node []))}})

(defmethod visit-mongo ::=lte= [context node]
  {(mongo-path node) {"$lte" (first (:arguments node []))}})

(defmethod visit-mongo ::=ex= [context node]
  {(mongo-path node) {"$exists" (first (:arguments node []))}})

(defmethod visit-mongo ::=q= [context node]
  {(mongo-path node) {"$elemMatch" (visit-mongo context (first (:arguments node)))}})

(defmulti visit-predicate
  (fn [_ {op :op}] op))

(defmethod visit-predicate ::or [context node]
  (apply some-fn (map (partial visit-predicate context) (:children node))))

(defmethod visit-predicate ::and [context node]
  (apply every-pred (map (partial visit-predicate context) (:children node))))

(defmethod visit-predicate ::== [context node]
  (fn [o] (= (get-in o (:path node)) (first (:arguments node)))))

(defmethod visit-predicate ::!= [context node]
  (fn [o] (not= (get-in o (:path node)) (first (:arguments node)))))

(defmethod visit-predicate ::=re= [context node]
  (fn [o]
    (boolean
      (re-matches (re-pattern (first (:arguments node)))
        (name (get-in o (:path node)))))))

(defmethod visit-predicate ::=in= [context node]
  (fn [o] (in (get-in o (:path node) []) (:arguments node []))))

(defmethod visit-predicate ::=out= [context node]
  (fn [o] (nin (get-in o (:path node) []) (:arguments node []))))

(defmethod visit-predicate ::=gt= [context node]
  (fn [o] (gt (get-in o (:path node)) (:arguments node))))

(defmethod visit-predicate ::=lt= [context node]
  (fn [o] (lt (get-in o (:path node)) (:arguments node))))

(defmethod visit-predicate ::=gte= [context node]
  (fn [o] (gte (get-in o (:path node)) (:arguments node))))

(defmethod visit-predicate ::=lte= [context node]
  (fn [o] (lte (get-in o (:path node)) (:arguments node))))

(defmethod visit-predicate ::=ex= [context node]
  (fn [o]
    (if (first (:arguments node))
      (some? (get-in o (:path node)))
      (nil? (get-in o (:path node))))))

(defmethod visit-predicate ::=q= [context node]
  (let [inner (visit-predicate context (first (:arguments node)))]
    (fn [o] (inner (get-in o (:path node))))))

(defn parse-predicate
  ([s] (parse-predicate s {}))
  ([s schema] (parse-predicate s schema {}))
  ([s schema context] (->> (parse s schema) (visit-predicate context) (comp boolean))))

(defn parse-mongodb
  ([s] (parse-mongodb s {}))
  ([s schema] (parse-mongodb s schema {}))
  ([s schema context] (->> (parse s schema) (visit-mongo context))))
