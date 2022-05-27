(ns ^:no-doc datalevin.pull-api
  (:require
   [datalevin.pull-parser :as dpp]
   #?(:clj  [datalevin.db :as db]
      :cljs [datalevin.db :as db :refer [DB]])
   #?(:clj  [datalevin.util :refer [cond+]]
      :cljs [datalevin.util :refer-macros [cond+]])
   [datalevin.lru :as lru]
   [datalevin.datom :as d]
   [datalevin.constants :as c]
   ;; [me.tonsky.persistent-sorted-set :as set]
   )
  #?(:clj
     (:import
      [clojure.lang ISeq]
      [datalevin.datom Datom]
      [datalevin.db DB]
      [datalevin.pull_parser PullAttr PullPattern])))

(declare pull-impl attrs-frame ref-frame ->ReverseAttrsFrame)

(defn- first-seq [#?(:clj xs :cljs ^seq xs)]
  (if (nil? xs)
    nil
    #?(:clj (first xs) :cljs (-first xs))))

(defn- next-seq [#?(:clj xs :cljs ^seq xs)]
  (if (nil? xs)
    nil
    #?(:clj (next xs) :cljs (-next xs))))

(defn- conj-seq [#?(:clj xs :cljs ^seq xs) x]
  (if (nil? xs)
    (list x)
    #?(:clj (conj xs x) :cljs (-conj xs x))))

(defn- assoc-some! [m k v]
  (if (nil? v) m (assoc! m k v)))

(defn- conj-some! [xs v]
  (if (nil? v) xs (conj! xs v)))

(defrecord Context [db visitor])

(defn visit [^Context context pattern e a v]
  (when-some [visitor (.-visitor context)]
    (visitor pattern e a v)))

(defprotocol IFrame
  (-merge [this result])
  (-run [this context]))

(defrecord ResultFrame [value datoms])

(defrecord MultivalAttrFrame [acc ^PullAttr attr datoms]
  IFrame
  (-run [this context]
    (loop [acc    acc
           datoms datoms]
      (cond+
        :let [^Datom datom (first-seq datoms)]

        (or (nil? datom) (not= (.-a datom) (.-name attr)))
        [(ResultFrame. ((.-xform attr) (not-empty (persistent! acc))) (or datoms ()))]

                                        ; got limit, skip rest of the datoms
        (and (.-limit attr) (>= (count acc) (.-limit attr)))
        (loop [datoms datoms]
          (let [^Datom datom (first-seq datoms)]
            (if (or (nil? datom) (not= (.-a datom) (.-name attr)))
              [(ResultFrame. (persistent! acc) (or datoms ()))]
              (recur (next-seq datoms)))))

        :else
        (recur (conj! acc (.-v datom)) (next-seq datoms))))))

(defrecord MultivalRefAttrFrame [seen recursion-limits acc pattern ^PullAttr attr datoms]
  IFrame
  (-merge [this result]
    (MultivalRefAttrFrame.
      seen
      recursion-limits
      (conj-some! acc (.-value ^ResultFrame result))
      pattern
      attr
      (next-seq datoms)))
  (-run [this context]
    (cond+
      :let [^Datom datom (first-seq datoms)]

      (or (nil? datom) (not= (.-a datom) (.-name attr)))
      [(ResultFrame. ((.-xform attr) (not-empty (persistent! acc))) (or datoms ()))]

                                        ; got limit, skip rest of the datoms
      (and (.-limit attr) (>= (count acc) (.-limit attr)))
      (loop [datoms datoms]
        (let [^Datom datom (first-seq datoms)]
          (if (or (nil? datom) (not= (.-a datom) (.-name attr)))
            [(ResultFrame. (persistent! acc) (or datoms ()))]
            (recur (next-seq datoms)))))

      :let [id (if (.-reverse? attr) (.-e datom) (.-v datom))]

      :else
      [this (ref-frame context seen recursion-limits pattern attr id)])))

(defrecord AttrsFrame [seen recursion-limits acc ^PullPattern pattern ^PullAttr attr attrs datoms id]
  IFrame
  (-merge [this result]
    (AttrsFrame.
      seen
      recursion-limits
      (assoc-some! acc (.-as attr) (.-value ^ResultFrame result))
      pattern
      (first-seq attrs)
      (next-seq attrs)
      (not-empty (or (.-datoms ^ResultFrame result) (next-seq datoms)))
      id))
  (-run [this context]
    (loop [acc    acc
           attr   attr
           attrs  attrs
           datoms datoms]
      (cond+
        ;; exit
        (and (nil? datoms) (nil? attr))
        [(->ReverseAttrsFrame seen recursion-limits acc pattern (first-seq (.-reverse-attrs pattern)) (next-seq (.-reverse-attrs pattern)) id)]

        ;; :db/id
        (and (some? attr) (= :db/id (.-name attr)))
        (recur (assoc! acc (.-as attr) ((.-xform attr) id)) (first-seq attrs) (next-seq attrs) datoms)

        :let [^Datom datom (first-seq datoms)
              cmp          (when (and datom attr)
                             (compare (.-name attr) (.-a datom)))
              attr-ahead?  (or (nil? attr) (and cmp (pos? cmp)))
              datom-ahead? (or (nil? datom) (and cmp (neg? cmp)))]

        ;; wildcard
        (and (.-wildcard? pattern) (some? datom) attr-ahead?)
        (let [datom-attr (lru/-get
                           (.-pull-attrs (.-db ^Context context))
                           (.-a datom)
                           #(dpp/parse-attr-name (.-db ^Context context) (.-a datom)))]
          (recur acc datom-attr (when attr (conj-seq attrs attr)) datoms))

        ;; advance datom
        attr-ahead?
        (recur acc attr attrs (next-seq datoms))

        :do (visit context :db.pull/attr id (.-name attr) nil)

        ;; advance attr
        (and datom-ahead? (nil? attr))
        (recur acc (first-seq attrs) (next-seq attrs) datoms)

        ;; default
        (and datom-ahead? (some? (#?(:clj .-default :cljs :default) attr)))
        (recur (assoc! acc (.-as attr) (#?(:clj .-default :cljs :default) attr)) (first-seq attrs) (next-seq attrs) datoms)

        ;; xform
        datom-ahead?
        (if-some [value ((.-xform attr) nil)]
          (recur (assoc! acc (.-as attr) value) (first-seq attrs) (next-seq attrs) datoms)
          (recur acc (first-seq attrs) (next-seq attrs) datoms))

        ;; matching attr
        (and (.-multival? attr) (.-ref? attr))
        [(AttrsFrame. seen recursion-limits acc pattern attr attrs datoms id)
         (MultivalRefAttrFrame. seen recursion-limits (transient []) pattern attr datoms)]

        (.-multival? attr)
        [(AttrsFrame. seen recursion-limits acc pattern attr attrs datoms id)
         (MultivalAttrFrame. (transient []) attr datoms)]

        (.-ref? attr)
        [(AttrsFrame. seen recursion-limits acc pattern attr attrs datoms id)
         (ref-frame context seen recursion-limits pattern attr (.-v datom))]

        :else
        (recur
          (assoc! acc (.-as attr) ((.-xform attr) (.-v datom)))
          (first-seq attrs)
          (next-seq attrs)
          (next-seq datoms))))))

(defrecord ReverseAttrsFrame [seen recursion-limits acc pattern ^PullAttr attr attrs id]
  IFrame
  (-merge [this result]
    (ReverseAttrsFrame.
      seen
      recursion-limits
      (assoc-some! acc (.-as attr) (.-value ^ResultFrame result))
      pattern
      (first-seq attrs)
      (next-seq attrs)
      id))
  (-run [this context]
    (loop [acc   acc
           attr  attr
           attrs attrs]
      (cond+
        (nil? attr)
        [(ResultFrame. (not-empty (persistent! acc)) nil)]

        :let [name   (.-name attr)
              db     (.-db ^Context context)
              datoms (db/-search db [nil name id])
              #_(if (instance? DB db)
                  (set/slice (.-avet ^DB db)
                             (d/datom c/e0 name id)
                             (d/datom c/emax name id))
                  (db/-search db [nil name id]))]

        :do (visit context :db.pull/reverse nil name id)

        (and (empty? datoms) (some? (#?(:clj .-default :cljs :default) attr)))
        (recur (assoc! acc (.-as attr) (#?(:clj .-default :cljs :default) attr)) (first-seq attrs) (next-seq attrs))

        (empty? datoms)
        (recur acc (first-seq attrs) (next-seq attrs))

        (.-component? attr)
        [(ReverseAttrsFrame. seen recursion-limits acc pattern attr attrs id)
         (ref-frame context seen recursion-limits pattern attr (.-e ^Datom (first-seq datoms)))]

        :else
        [(ReverseAttrsFrame. seen recursion-limits acc pattern attr attrs id)
         (MultivalRefAttrFrame. seen recursion-limits (transient []) pattern attr datoms)]))))

(defn- auto-expanding? [^PullAttr attr]
  (or
    (.-recursive? attr)
    (and
      (.-component? attr)
      (.-wildcard? ^PullPattern (.-pattern attr)))))

(defn ref-frame [context seen recursion-limits pattern ^PullAttr attr id]
  (cond+
    (not (auto-expanding? attr))
    (attrs-frame context seen recursion-limits (.-pattern attr) id)

    (seen id)
    (ResultFrame. {:db/id id} nil)

    :let [lim (recursion-limits attr)]

    (and lim (<= lim 0))
    (ResultFrame. nil nil)

    :let [seen' (conj seen id)
          recursion-limits' (cond
                              lim                      (update recursion-limits attr dec)
                              (.-recursion-limit attr) (assoc recursion-limits attr (dec (.-recursion-limit attr)))
                              :else                    recursion-limits)]

    :else
    (attrs-frame context seen' recursion-limits' (if (.-recursive? attr) pattern (.-pattern attr)) id)))


(defn attrs-frame [^Context context seen recursion-limits ^PullPattern pattern id]
  (let [db     (.-db context)
        schema (db/-schema db)
        datoms (cond+
                 ;; (and (.-wildcard? pattern) (instance? DB db))
                 ;; (set/slice (.-eavt ^DB db) (d/datom id nil nil)
                 ;;            (d/datom id nil nil))

                 (.-wildcard? pattern)
                 (db/-search db [id])

                 (nil? (.-first-attr pattern))
                 nil

                 :let [from (.-name ^PullAttr (.-first-attr pattern))
                       to   (.-name ^PullAttr (.-last-attr pattern))
                       from-aid (:db/aid (schema from))
                       to-aid (:db/aid (schema to))]

                 (and from-aid to-aid (<= from-aid to-aid))
                 (db/-datom-range db :eavt (d/datom id from c/v0)
                                  (d/datom id to c/vmax))

                 ;; (instance? DB db)
                 ;; (db/-datom-range db :eavt (d/datom id from c/v0)
                 ;;                  (d/datom id to c/vmax))
                 ;; (set/slice (.-eavt ^DB db) (d/datom id from nil)
                 ;;            (d/datom id to nil))

                 (and from-aid to-aid (> from-aid to-aid))
                 (db/-datom-range db :eavt (d/datom id to c/v0)
                                  (d/datom id from c/vmax))

                 :else
                 (->> (db/-seek-datoms db :eavt [id]))
                 (take-while
                   (fn [^Datom d]
                     (and
                       (= (.-e d) id)
                       (<= (compare (.-a d) to) 0)
                       ;; (>= (compare (.-a d) from) 0)
                       )))
                 )]
    (when (.-wildcard? pattern)
      (visit context :db.pull/wildcard id nil nil))
    (AttrsFrame.
      seen
      recursion-limits
      (transient {})
      pattern
      (first-seq (.-attrs pattern))
      (next-seq (.-attrs pattern))
      datoms
      id)))

(defn pull-impl [parsed-opts id]
  (let [{^Context context     :context
         ^PullPattern pattern :pattern} parsed-opts]
    (when-some [eid (db/entid (.-db context) id)]
      (loop [stack (list (attrs-frame context #{} {} pattern eid))]
        (cond+
          :let [last   (first-seq stack)
                stack' (next-seq stack)]

          (not (instance? ResultFrame last))
          (recur (reduce conj-seq stack' (-run last context)))

          (nil? stack')
          (.-value ^ResultFrame last)

          :let [penultimate (first-seq stack')
                stack''     (next-seq stack')]

          :else
          (recur (conj-seq stack'' (-merge penultimate last))))))))

(defn parse-opts
  ([db pattern] (parse-opts db pattern nil))
  ([db pattern {:keys [visitor]}]
   {:pattern (lru/-get (.-pull-patterns db) pattern #(dpp/parse-pattern db pattern))
    :context (Context. db visitor)}))

(defn pull
  "Supported opts:

   :visitor a fn of 4 arguments, will be called for every entity/attribute pull touches

   (:db.pull/attr     e   a   nil) - when pulling a normal attribute, no matter if it has value or not
   (:db.pull/wildcard e   nil nil) - when pulling every attribute on an entity
   (:db.pull/reverse  nil a   v  ) - when pulling reverse attribute"
  ([db pattern id] (pull db pattern id {}))
  ([db pattern id opts]
   {:pre [(db/db? db)]}
   (let [parsed-opts (parse-opts db pattern opts)]
     (pull-impl parsed-opts id))))

(defn pull-many
  ([db pattern ids] (pull-many db pattern ids {}))
  ([db pattern ids opts]
   {:pre [(db/db? db)]}
   (let [parsed-opts (parse-opts db pattern opts)]
     (mapv #(pull-impl parsed-opts %) ids))))

(comment
  (do
    (set! *warn-on-reflection* true)
    (require 'datascript.test :reload-all)
    (binding [clojure.test/*report-counters* (ref clojure.test/*initial-report-counters*)]
      (clojure.test/test-vars
        [#'datascript.test.pull-parser/test-parse-pattern
         #'datascript.test.pull-api/test-pull-attr-spec
         #'datascript.test.pull-api/test-pull-reverse-attr-spec
         #'datascript.test.pull-api/test-pull-component-attr
         #'datascript.test.pull-api/test-pull-wildcard
         #'datascript.test.pull-api/test-pull-limit
         #'datascript.test.pull-api/test-pull-default
         #'datascript.test.pull-api/test-pull-as
         #'datascript.test.pull-api/test-pull-attr-with-opts
         #'datascript.test.pull-api/test-pull-map
         #'datascript.test.pull-api/test-pull-recursion
         #'datascript.test.pull-api/test-dual-recursion
         #'datascript.test.pull-api/test-deep-recursion
         #'datascript.test.pull-api/test-lookup-ref-pull
         ])
      @clojure.test/*report-counters*)))
