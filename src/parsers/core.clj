(ns parsers.core
  (:require [schema.core :as s]
            [clojure.string :as string]
            [clojure.core.memoize :as memo]
            [clojure.pprint :refer [pprint]]
            [clojure.set :as sets])
  (:import (cz.jirutka.rsql.parser.ast RSQLOperators ComparisonOperator Node AndNode OrNode ComparisonNode)
           (cz.jirutka.rsql.parser RSQLParser)
           (java.time.format DateTimeFormatter)
           (java.time Instant)))


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
      (first (filter #{::string ::boolean ::number ::date} [hint])))))

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

(defn coerce-string [s] (identity s))

(defn coerce-boolean [s]
  (boolean (Boolean/valueOf ^String s)))

(defn coerce-number [s]
  (try
    (Long/parseLong s)
    (catch Exception e
      (Double/parseDouble s))))

(defn coerce-date [s]
  (let [parser (DateTimeFormatter/ISO_DATE_TIME)]
    (Instant/from (.parse parser s))))

(defn best-effort [s]
  (letfn [(attempt [s queue]
            (try
              ((first queue) s)
              (catch Exception _
                (attempt s (rest queue)))))]
    (attempt s [coerce-date coerce-number coerce-boolean coerce-string])))

(defn coerce-guess [n]
  (coerce-node best-effort n))

(defn coerce-schema [n]
  (coerce-node coerce-string n))

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
    (has-schema? context n) (coerce-schema n)
    :else (coerce-guess n)))

(defn coerce-argument-types
  ([tree] (coerce-argument-types tree {}))
  ([tree schema] (visit-coercion {:schema schema} tree)))

(defn parse-to-tree [s]
  (-> (get-operators) (RSQLParser.) (.parse s) (node->data)))

(defn parse
  ([s] (parse s {}))
  ([s schema] (-> s (parse-to-tree) (coerce-argument-types schema))))


;;; predicates

(defn coll-like? [x]
  (and (not (string? x)) (try (seq x) (catch Exception _))))

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

(defn compare-coll [op]
  (fn [provided value]
    (if (and (coll-like? provided) (coll-like? value))
      (op (count provided) (count value))
      (op (first provided) (first value)))))

(defn gt [provided value]
  ((compare-coll >) provided value))

(defn lt [provided value]
  ((compare-coll <) provided value))

(defn gte [provided value]
  ((compare-coll >=) provided value))

(defn lte [provided value]
  ((compare-coll <=) provided value))

(defmulti visit-predicate
  (fn [_ {op :op}] op))

(defmethod visit-predicate ::or [context node]
  (apply some-fn (map (partial visit-predicate context) (:children node))))

(defmethod visit-predicate ::and [context node]
  (apply every-pred (map (partial visit-predicate context) (:children node))))

(defmethod visit-predicate ::== [node context]
  (fn [o]
    (= (get-in o (:path node))
      (first (:arguments node)))))

(defmethod visit-predicate ::!= [context node]
  (fn [o] (not= (get-in o (:path node)) (first (:arguments node)))))

(defmethod visit-predicate ::=re= [context node]
  (fn [o] (boolean
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
  (fn [o]
    ((visit-predicate context
       (first (:arguments node)))
      (get-in o (:path node)))))

(defn parse-predicate
  ([s] (parse-predicate s {}))
  ([s schema] (parse-predicate s schema {}))
  ([s schema context] (-> s (parse schema) (visit-predicate context))))
