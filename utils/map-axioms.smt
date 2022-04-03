; map definitions
(define-sort Map (K V) (Tuple2 (Set K) (Array K V)))

(define-sort K () Int)
(define-sort V () Int)

(define-fun map_create ( ) (Map K V)
  (tuple2 (as set.empty (Set K)) ((as const (Array K V)) 0)))

(define-fun map_contains ( (m (Map K V)) (k K) ) Bool
  (set.member k (tuple2_get0 m)))

(declare-fun map_values ( (m (Map K V)) ) (MLList V))
(assert (forall ( (m (Map K V)) )
  (= (set.card (tuple2_get0 m)) (list_length (map_values m)))))
(assert (forall ( (m (Map K V)) (k K) )
  (=> (set.member k (tuple2_get0 m)) (list_contains (map_values m) (select (tuple2_get1 m) k)))))

(define-fun map_get ( (m (Map K V)) (k K) (d V) ) V (ite
  (set.member k (tuple2_get0 m))
  (select (tuple2_get1 m) k)
  d
))

(define-fun map_get_direct ( (m (Map K V)) (k K) (d V) ) V (select (tuple2_get1 m) k))
