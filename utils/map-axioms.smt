; map definitions
(declare-datatypes ((Map 2)) ((par (K V) ((make_map (map_internal_keys (Set K)) (map_internal_array (Array K V)))))))
;(define-sort Map (K V) (make_map (Set K) (Array K V)))

(define-sort K_Map () Int)
(define-sort V_Map () Int)

(define-fun map_create ( ) (Map K_Map V_Map)
  (make_map (as set.empty (Set K_Map)) ((as const (Array K_Map V_Map)) 0)))

(define-fun map_contains ( (m (Map K_Map V_Map)) (K_Map K_Map) ) Bool
  (set.member K_Map (map_internal_keys m)))

(declare-fun map_values ( (Map K_Map V_Map) ) (MLList V_Map))
(assert (forall ( (m (Map K_Map V_Map)) )
  (= (set.card (map_internal_keys m)) (list_length (map_values m)))))
(assert (forall ( (m (Map K_Map V_Map)) (K_Map K_Map) )
  (=> (set.member K_Map (map_internal_keys m)) (list_contains (map_values m) (select (map_internal_array m) K_Map)))))

(define-fun map_get ( (m (Map K_Map V_Map)) (K_Map K_Map) (d V_Map) ) V_Map (ite
  (set.member K_Map (map_internal_keys m))
  (select (map_internal_array m) K_Map)
  d
))

(define-fun map_get_direct ( (m (Map K_Map V_Map)) (K_Map K_Map) (d V_Map) ) V_Map (select (map_internal_array m) K_Map))
