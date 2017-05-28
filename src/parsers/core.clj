(ns parsers.core
  (:require [schema.core :as s]
            [clojure.string :as string]
            [clojure.core.memoize :as memo]
            [clojure.pprint :refer [pprint]])
  (:import (cz.jirutka.rsql.parser.ast RSQLOperators ComparisonOperator Node AndNode OrNode ComparisonNode)
           (cz.jirutka.rsql.parser RSQLParser)
           (java.time.format DateTimeFormatter)
           (java.time Instant)))

(derive ::or ::logical)
(derive ::and ::logical)
(derive ::== ::comparison)
(derive ::!= ::comparison)
(derive ::=q= ::comparison)
(derive ::=gt= ::comparison)
(derive ::=ge= ::comparison)
(derive ::=lt= ::comparison)
(derive ::=le= ::comparison)
(derive ::=ft= ::comparison)
(derive ::=re= ::comparison)
(derive ::=ex= ::comparison)
(derive ::=in= ::comparison)
(derive ::=out= ::comparison)

(defn get-namespace []
  (namespace ::_))

(defn keify [k]
  (keyword (get-namespace) (name k)))

(defn get-operators []
  (set (conj (into #{} (RSQLOperators/defaultOperators))
             (ComparisonOperator. (into-array String ["=ex="]))
             (ComparisonOperator. (into-array String ["=re="]))
             (ComparisonOperator. (into-array String ["=q="])))))

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

(defn has-schema? [context]
  (some? (get context :schema)))

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

(defn coerce-guess [n]
  (coerce-node coerce-string n))

(defn coerce-schema [n]
  (coerce-node coerce-string n))

(defn coerce-hint [n]
  (condp = (get (second n) :hint)
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
  (let [parent-context (assoc context :parent (get n :path))]
    (coerce-node #(visit-coercion context (parse-to-tree %)) n)))

(defmethod visit-coercion ::comparison [context n]
  (cond
    (has-schema? context) (coerce-schema n)
    (has-type-hint? n) (coerce-hint n)
    :else (coerce-guess n)))

(defn coerce-argument-types
  ([tree] (coerce-argument-types tree {}))
  ([tree schema] (visit-coercion {:schema schema} tree)))

(defn parse-to-tree [s]
  (-> (get-operators) (RSQLParser.) (.parse s) (node->data)))

(def parse
  (memo/lru
    (fn
      ([s] (parse s {}))
      ([s schema]
       (-> s (parse-to-tree) (coerce-argument-types schema))))
    {} :lru/threshold 1000))


