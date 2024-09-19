(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "arithmetic/top" :dir :system)
;; idk why the following two books are necessary
(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "centaur/bitops/fast-logext" :dir :system)

(include-book "ihs/logops-lemmas" :dir :system)
(include-book "centaur/bitops/part-select" :DIR :SYSTEM)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

(include-book "centaur/fgl/top" :dir :system)

(include-book "srl")
(include-book "../sra-sign")

;;;;;;;;;;;;;
;;
;; Chunking and append
;;
;;;;;;;;;;;;;

(gl::def-gl-thm sra-sign-32-chunk-correctness
  :hyp (unsigned-byte-p 32 x)
  :concl (equal (logbit 7 (part-select x :low 24 :width 8))
                (logbit 31 x))
  :g-bindings (gl::auto-bindings (:nat x 32)))

(define sra-chunk-lookup-combine-32 (x y)
  :verify-guards nil
  :enabled t
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p  5 y)) 0)
       ;; setup subtables
       (indices (create-x-indices (expt 2 8) (expt 2 5)))
         ;; SRL subtables
       (subtable-0 (create-srli-subtable indices  0))
       (subtable-1 (create-srli-subtable indices  8))
       (subtable-2 (create-srli-subtable indices 16))
       (subtable-3 (create-srli-subtable indices 24))
       (subtable-4 (materialize-sra-sign-subtable-32 indices))
         ;; SRA-sign-subtables
       ;; chunk
       (u8-0 (part-select x :low  0 :width 8))
       (u8-1 (part-select x :low  8 :width 8))
       (u8-2 (part-select x :low 16 :width 8))
       (u8-3 (part-select x :low 24 :width 8))
       ;; lookup chunks
       (sign (lookup u8-3 y subtable-4))
       (u8-0 (lookup u8-0 y subtable-0))
       (u8-1 (lookup u8-1 y subtable-1))
       (u8-2 (lookup u8-2 y subtable-2))
       (u8-3 (lookup u8-3 y subtable-3)))
       ;; add chunks
      (+ sign u8-3 u8-2 u8-1 u8-0)))

;(gl::def-gl-thm silly-bounds-lemma-due-to-logtail-rewrite
; :hyp  (and (integerp x)
;               (<= 0 x)
;               (< x 4294967296))
; :concl (not (< 256 (logtail 24 x)))
; :g-bindings (gl::auto-bindings (:nat x 32)))
;
;(gl::def-gl-thm silly-logtail-rewrite
; :hyp  (and (integerp x)
;               (<= 0 x)
;               (< x 4294967296))
; :concl (equal (logtail 24 x)
;	       (part-select x :low 24 :width 8))
; :g-bindings (gl::auto-bindings (:nat x 32)))

;(local (in-theory (disable 
;;		    LOGHEAD$INLINE
;		    silly-logtail-rewrite
;		    ;LOGTAIL$INLINE
;		    ;BITOPS::PART-SELECT-WIDTH-LOW$INLINE
;		    )))
(defthm sra-srl-equiv
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 5 y))
	  (equal (sra-chunk-lookup-combine-32 x y)
	         (+ (sra-sign-8 (part-select x :low 24 :width 8) y)
	            (srl-chunk-lookup-combine-32 x y))))
 :hints (("GoaL" 
	         :do-not-induct t
	         :in-theory (e/d ();sra-sign-8)
				 ((:e create-x-indices)
				  (:e create-srli-subtable))))))

(defthm sra-correctness-1
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 5 y))
	  (equal (sra-chunk-lookup-combine-32 x y)
	         (+ (sra-sign-8 (part-select x :low 24 :width 8) y)
	            (ash x (- y)))))
 :hints (("GoaL" :use ((:instance srl-chunk-lookup-combine-32-correctness))
	         :in-theory (e/d ();sra-sign-8)
				 ((:e create-x-indices)
				  (:e create-srli-subtable))))))


(defthm sra-correctness-2
 (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 5 y))
	  (equal (sra-chunk-lookup-combine-32 x y)
		 (logextu 32 (- 32 y) (ash x (- y)))))
 :hints (("GoaL" :use ((:instance sra-sign-8-correctness)
		       (:instance sra-correctness-1))
	         :in-theory (e/d ();sra-sign-8)
				 ((:e create-x-indices)
				  (:e create-srli-subtable))))))
