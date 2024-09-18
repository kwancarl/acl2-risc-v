(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)

;; MATERIALIZE SUBTABLES FOR "Sign-extend"

(include-book "centaur/gl/gl" :dir :system)
(local (include-book "ihs/basic-definitions" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/fast-logext" :dir :system))


(include-book "eq")
(include-book "subtable")


;(local (include-book "arithmetic/top" :dir :system))
;(local (include-book "ihs/logops-lemmas" :dir :system))




;; SRA-sign intended function & MLE correctness

;; 1...1 0...0
;; w - k   k
;; w = 32
(define masked-ones-slow ((k natp) (w natp))
  :guard (< k w)
  :enabled t
  (mbe
    :logic (if (not (and (natp k) (natp w) (< k w)))
               0
               (if (zp k)
                   0
                   (+ (expt2 (- w k)) (masked-ones-slow (1- k) w))))
    :exec (if (zp k) 
	      0 
	      (+ (expt2 (- w k)) (masked-ones-slow (1- k) w)))))

(define masked-ones ((k natp) (w natp))
  :enabled t
  (mbe 
   :logic (if (not (natp w))
              0
              (if (zp w) 
		  0
		  (if (< k w)
      	              (logcons 0 (masked-ones k (1- w)))
      	              (logcons 1 (masked-ones k (1- w))))))
   :exec (if (zp w)
              0
              (if (< k w)
      	          (logcons 0 (masked-ones k (1- w)))
      	          (logcons 1 (masked-ones k (1- w)))))))

(defthm natp-of-expt2-when-nat
 (implies (natp w) (natp (expt2 w))))

(define masked-ones-fast ((k natp) (w natp))
  :guard-hints (("Goal" :use ((:instance natp-of-expt2-when-nat))))
  (mbe 
   :logic
    (if (not (and (natp k) (natp w)))
        0
        (ash (ash (1- (expt2 w)) (- k w)) (- w k)))
   :exec
    (ash (ash (1- (expt2 w)) (- k w)) (- w k))))


(local (in-theory (enable logcons)))

;(en
;(defthm masked-ones-slow-and-fast
; (implies (and (natp w) (natp k) (< k w))
;	  (equal (masked-ones-slow k w) (masked-ones k w)))
; :hints (("Subgoal *1/4" :expand (masked-ones k w))))
;:i-am-here

(define sra-sign-helper ((sign bitp) (y natp) (k natp) (w natp))
 (if (zp k)
     (* (eqw k y) sign (masked-ones k w))
     (+ (* (eqw k y) sign (masked-ones k w))
        (sra-sign-helper sign y (1- k) w)))
 ///

 (local (in-theory (enable eqw-equal-equiv)))

 (local (defthm sra-sign-helper-when-k-<-y
  (implies (and (natp y) (natp k) (< k y))
           (equal (sra-sign-helper sign y k w) 0))))

 (local (defthm sra-sign-helper-when-k-=-y
  (implies (and (natp y) (natp k) (= k y))
           (equal (sra-sign-helper sign y k w) 
		  (* sign (masked-ones y w))))))

 (local (defthm sra-sign-helper-when-y-<-k
  (implies (and (natp y) (natp k) (< y k))
           (equal (sra-sign-helper sign y k w)
		  (* sign (masked-ones y w))))))
 
 (defthm sra-sign-helper-correctness
  (implies (and (natp y) (natp k))
           (equal (sra-sign-helper sign y k w)
                  (if (< k y)
                      0
                      (* sign (masked-ones y w)))))))



;(include-book "centaur/fgl/top" :dir :system)
;(value-triple (acl2::tshell-ensure))

(gl::def-gl-thm masked-one-easy-gl
 :hyp (unsigned-byte-p 5 y)
 :concl (equal (masked-ones y 32)
	       (masked-ones-fast y 32))
 :g-bindings (gl::auto-bindings (:nat y 5)))

;:i-am-here
;
;(gl::def-gl-param-thm masked-one-fast-and-slow
; :hyp (unsigned-byte-p 5 y)
; :concl (equal (masked-ones y 32)
;	       (masked-ones-fast y 32))
; :param-bindings
; `((((low  0) (high  8)) ,(gl::auto-bindings (:nat y 5)))
;   (((low  8) (high 12)) ,(gl::auto-bindings (:nat y 5)))
;   (((low 12) (high 32)) ,(gl::auto-bindings (:nat y 5)))
;   )
; :param-hyp (and (<= low y) (< y high))
; :cov-bindings (gl::auto-bindings (:nat y 5)))
;:i-am-here


;(fgl::def-fgl-thm logbitp-<-equiv-1
; :hyp (and (unsigned-byte-p 24 x)
;	   (logbitp 23 x))
; :concl (and (<= (expt 2 23) x)
;	     (<  x (expt 2 24))))


;(fgl::def-fgl-thm logbitp-<-equiv-2
; :hyp (and (unsigned-byte-p 25 x)
;	   (<= (expt 2 24) x)   
;	   (<  x (expt 2 25)))
; :concl (logbitp 24 x))

;(gl::def-gl-param-thm masked-ones-correctness
;  :hyp (and (unsigned-byte-p 5 y) 
;	    (unsigned-byte-p 32 x))
;  :concl (equal (logextu 32 (- 32 y) (ash x (- y)))
;		(+ (* (logbit 31 x) (masked-ones y 32))
;		   (ash x (- y))))
; :param-bindings
; `((((low  0) (high 32)) ,(gl::auto-bindings (:nat y 5) (:nat x 32))))
;   ;(((low 16) (high 32)) ,(gl::auto-bindings (:nat y 5) (:nat x 32))))
; :param-hyp (and (<= low y) (< y high))
; :cov-bindings (gl::auto-bindings (:nat y 5) (:nat x 32)))

(gl::def-gl-thm masked-ones-correctness
  :hyp (and (unsigned-byte-p 5 y) 
	    (unsigned-byte-p 32 x))
  :concl (equal (logextu 32 (- 32 y) (ash x (- y)))
		(+ (* (logbit 31 x) (masked-ones y 32))
		   (ash x (- y))))
  :g-bindings (gl::auto-bindings (:nat y 5) (:nat x 32)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;					;;
;;    MATERIALIZE SRA-SIGN SUBTABLES    ;;
;;					;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;(define sign-extend-idx (z-hi width)
; :enabled t
; :returns (lst alistp)
; :measure (acl2-count z-hi)
; (if (not (natp z-hi))
;     nil
;     (if (zerop z-hi)
;         (cons (cons z-hi width) nil)
;         (cons (cons z-hi width) 
;               (sign-extend-idx (1- z-hi) width)))))
;
;(defthm sign-extend-idx-correctness
; (implies (and (natp z-hi) 
;               (natp i) 
;               (<= i z-hi))
;          (member (cons i width) (sign-extend-idx z-hi width))))
;
;(defun materialize-sign-extend-subtable-32 (idx-lst)
; (b* (((unless (alistp idx-lst))     nil)
;      ((if (atom idx-lst))           nil)
;      ((cons idx rst)            idx-lst)
;      ((unless (consp idx))          nil)
;      ((cons z width)                 idx))
;     (cons (cons idx (logtail width (logextu 32 width z)))
;           (materialize-sign-extend-subtable-32 rst))))
;
;(defun materialize-sign-extend-subtable-64 (idx-lst)
; (b* (((unless (alistp idx-lst))     nil)
;      ((if (atom idx-lst))           nil)
;      ((cons idx rst)            idx-lst)
;      ((unless (consp idx))          nil)
;      ((cons z width)                 idx))
;     (cons (cons idx (logtail width (logextu 64 width z)))
;           (materialize-sign-extend-subtable-64 rst))))
;
;(defthm alistp-of-materialize-sign-extend-subtable-32
; (alistp (materialize-sign-extend-subtable-32 idx-lst)))
;
;(defthm alistp-of-materialize-sign-extend-subtable-64
; (alistp (materialize-sign-extend-subtable-64 idx-lst)))
;
;(defthm member-idx-lst-assoc-materialize-sign-extend-subtable-32
; (implies (and (alistp idx-lst) (member idx idx-lst))
;          (assoc idx (materialize-sign-extend-subtable-32 idx-lst))))
;
;(defthm member-idx-lst-assoc-materialize-sign-extend-subtable-64
; (implies (and (alistp idx-lst) (member idx idx-lst))
;          (assoc idx (materialize-sign-extend-subtable-64 idx-lst))))
;
;(defthm assoc-member-materialize-sign-extend-subtable-32
; (implies (assoc (cons z width) (materialize-sign-extend-subtable-32 idx-lst))
;          (member (cons z width) idx-lst)))
;
;(defthm assoc-member-materialize-sign-extend-subtable-64
; (implies (assoc (cons z width) (materialize-sign-extend-subtable-64 idx-lst))
;          (member (cons z width) idx-lst)))
;
;(defthm assoc-materialize-sign-extend-subtable-32
; (implies (assoc (cons i width) (materialize-sign-extend-subtable-32 idx-lst))
;          (equal (assoc (cons i width) (materialize-sign-extend-subtable-32 idx-lst))
;                 (cons (cons i width) (logtail width (logextu 32 width i))))))
;
;(defthm assoc-materialize-sign-extend-subtable-64
; (implies (assoc (cons i width) (materialize-sign-extend-subtable-64 idx-lst))
;          (equal (assoc (cons i width) (materialize-sign-extend-subtable-64 idx-lst))
;                 (cons (cons i width) (logtail width (logextu 64 width i))))))
;
;(defthm materialize-sign-extend-subtable-32-correctness
; (implies (and (natp z-hi) 
;               (natp i) 
;               (<= i z-hi))
;          (b* ((indices  (sign-extend-idx z-hi width))
;               (subtable (materialize-sign-extend-subtable-32 indices)))
;              (equal (assoc-equal (cons i width) subtable)
;                     (cons (cons i width)
;                           (logtail width (logextu 32 width i)))))))
;
;(defthm materialize-sign-extend-subtable-64-correctness
; (implies (and (natp z-hi) 
;               (natp i) 
;               (<= i z-hi))
;          (b* ((indices  (sign-extend-idx z-hi width))
;               (subtable (materialize-sign-extend-subtable-64 indices)))
;              (equal (assoc-equal (cons i width) subtable)
;                     (cons (cons i width)
;                           (logtail width (logextu 64 width i)))))))
;                 
;(defthm lookup-materialize-sign-extend-subtable-32-correctness
; (implies (and (natp z-hi) 
;               (natp i) 
;               (<= i z-hi))
;          (b* ((indices  (sign-extend-idx z-hi width))
;               (subtable (materialize-sign-extend-subtable-32 indices)))
;              (equal (lookup i width subtable)
;                     (logtail width (logextu 32 width i)))))
; :hints (("Goal" :in-theory (e/d (lookup) ()))))
;
;(defthm lookup-materialize-sign-extend-subtable-64-correctness
; (implies (and (natp z-hi) 
;               (natp i) 
;               (<= i z-hi))
;          (b* ((indices  (sign-extend-idx z-hi width))
;               (subtable (materialize-sign-extend-subtable-64 indices)))
;              (equal (lookup i width subtable)
;                     (logtail width (logextu 64 width i)))))
; :hints (("Goal" :in-theory (e/d (lookup) ()))))


;; CORRECTNESS OF SUBTABLES WRT LOGAPP

;(defthmd loghead-logextu-reverse-32
;  (implies (and (<= width 32)
;                (logextu-guard 32 width i)
;                (natp width))
;           (equal (loghead width i)
;                  (loghead width (logextu 32 width i)))))
;
;(defthmd loghead-logextu-reverse-64
;  (implies (and (<= width 64)
;                (logextu-guard 64 width i)
;                (natp width))
;           (equal (loghead width i)
;                  (loghead width (logextu 64 width i)))))
;
;(defthm logapp-materialize-sign-extend-subtable-64-correctness
; (implies (and (natp i) 
;               (natp z-hi) 
;               (natp width)
;               (<= i z-hi)
;               (<= width 64))
;          (b* ((indices  (sign-extend-idx z-hi width))
;               (subtable (materialize-sign-extend-subtable-64 indices)))
;              (equal (logapp width 
;                             (loghead width i)
;                             (lookup i width subtable))
;                     (logextu 64 width i))))
; :hints (("Goal" :use ((:instance loghead-logextu-reverse-64))
;                 :in-theory (disable logextu
;                                     loghead-logextu 
;                                     bitops::logapp-of-loghead))))
;
;(defthm logapp-materialize-sign-extend-subtable-32-correctness
; (implies (and (natp i) 
;               (natp z-hi) 
;               (natp width)
;               (<= i z-hi)
;               (<= width 32))
;          (b* ((indices  (sign-extend-idx z-hi width))
;               (subtable (materialize-sign-extend-subtable-32 indices)))
;              (equal (logapp width 
;                             (loghead width i)
;                             (lookup i width subtable))
;                     (logextu 32 width i))))
; :hints (("Goal" :use ((:instance loghead-logextu-reverse-32))
;                 :in-theory (disable logextu
;                                     loghead-logextu 
;                                     bitops::logapp-of-loghead))))
;



