(in-package "ACL2")
;(include-book "std/util/bstar" :dir :system)
;(include-book "std/util/define" :dir :system)
(include-book "operations")
(include-book "rv-state")
;(ld "add.lisp")

;; CK: Proof infrastructure from BY
;;     for byte-addressable memory model
(defun n32p-n08p-alistp (alst)
  ;; Recognizes an alist of form: ( (addr . value) ... ). 
  ;; Each addr must be an n32p and each value a n08p.
  (declare (xargs :guard t))
  (if (atom alst)
      t
    (if (atom (car alst))
        nil
      (let ((symbol (caar alst))
            (val    (cdar alst))
            (rest   (cdr  alst)))
        (and (n32p symbol)
             (n08p val)
             (n32p-n08p-alistp rest))))))

(defun n32p-listp (lst)
  (if (atom lst)
      t
    (and (n32p (car lst))
         (n32p-listp (cdr lst)))))

(defun n32p-n08p-alist-list-keys (alst)
  (if (atom alst)
      nil
    (cons (caar alst)
          (n32p-n08p-alist-list-keys (cdr alst)))))

(defthm n32p-n08p-alist-list-keys-n32p-listp
  (implies (n32p-n08p-alistp alst)
           (n32p-listp (n32p-n08p-alist-list-keys alst))))

(defun rv32-mem-program-bytes-loadedp (program-bytes rv32)
  ;; Given an alist of the form ( ... (addr . byte-value) ... ), this
  ;; predicate checks whether it's loaded into the rv32 memory.
  (declare (xargs :stobjs (rv32)
                  :guard (n32p-n08p-alistp program-bytes)))
  (if (atom program-bytes)
      t
    (let ((addr (caar program-bytes))
          (val  (cdar program-bytes))
          (rest (cdr  program-bytes)))
      (and (equal (rm08 addr rv32) val)
           (rv32-mem-program-bytes-loadedp rest rv32)))))

;(defun n32p-n32p-alistp (alst)
;  ;; Recognizes an alist of form: ( (addr . value) ... ). 
;  ;; Each addr must be an n32p and each value a n32p.
;  (declare (xargs :guard t))
;  (if (atom alst)
;      t
;    (if (atom (car alst))
;        nil
;      (let ((symbol (caar alst))
;            (val    (cdar alst))
;            (rest   (cdr  alst)))
;        (and (n32p symbol)
;             (n32p val)
;             (n32p-n32p-alistp rest))))))
;
;(defun n32p-listp (lst)
;  (if (atom lst)
;      t
;    (and (n32p (car lst))
;         (n32p-listp (cdr lst)))))
;
;(defun n32p-n32p-alist-list-keys (alst)
;  (if (atom alst)
;      nil
;    (cons (caar alst)
;          (n32p-n32p-alist-list-keys (cdr alst)))))
;
;(defthm n32p-n32p-alist-list-keys-n32p-listp
;  (implies (n32p-n32p-alistp alst)
;           (n32p-listp (n32p-n32p-alist-list-keys alst))))
;
;(defun rv32-mem-program-instr-loadedp (program-instr rv32)
;  ;; Given an alist of the form ( ... (addr . instr-value) ... ), this
;  ;; predicate checks whether it's loaded into the rv32 memory.
;  (declare (xargs :stobjs (rv32)
;                  :guard (n32p-n32p-alistp program-instr)))
;  (if (atom program-instr)
;      t
;    (let ((addr (caar program-instr))
;          (val  (cdar program-instr))
;          (rest (cdr  program-instr)))
;      (and (equal (rm32 addr rv32) val)
;           (rv32-mem-program-instr-loadedp rest rv32)))))





;; CK: Proof infrastructure for word-addressable memory model
(defun n32p-n32p-alistp (alst)
  ;; Recognizes an alist of form: ( (addr . value) ... ). 
  ;; Each addr must be an n32p and each value a n32p.
  ;; Note: We do not restrict addr to increase by 4 here
  (declare (xargs :guard t))
  (if (atom alst)
      t
    (if (atom (car alst))
        nil
      (let ((symbol (caar alst))
            (val    (cdar alst))
            (rest   (cdr  alst)))
        (and (n32p symbol)
             (n32p val)
             (n32p-n32p-alistp rest))))))

;(defun n32p-listp (lst)
;  (if (atom lst)
;      t
;    (and (n32p (car lst))
;         (n32p-listp (cdr lst)))))
;
;(defun n32p-n32p-alist-list-keys (alst)
;  (if (atom alst)
;      nil
;    (cons (caar alst)
;          (n32p-n32p-alist-list-keys (cdr alst)))))
;
;(defthm n32p-n32p-alist-list-keys-n32p-listp
;  (implies (n32p-n32p-alistp alst)
;           (n32p-listp (n32p-n32p-alist-list-keys alst))))
;
;(defun rv32-mem-program-words-loadedp (program-bytes rv32)
;  ;; Given an alist of the form ( ... (addr . word-value) ... ), this
;  ;; predicate checks whether it's loaded into the rv32 memory.
;  (declare (xargs :stobjs (rv32)
;		  :verify-guards nil
;                  :guard (n32p-n32p-alistp program-bytes)))
;  (if (atom program-bytes)
;      t
;    (let ((addr (caar program-bytes))
;          (val  (cdar program-bytes))
;          (rest (cdr  program-bytes)))
;      (and (equal (rm32 addr rv32) val)
;           (rv32-mem-program-bytes-loadedp rest rv32)))))



;; I think the below is repeated

(defun n32p-n32p-alistp (alst)
  ;; Recognizes an alist of form: ( (addr . value) ... ). 
  ;; Each addr must be an n32p and each value a n32p.
  (declare (xargs :guard t))
  (if (atom alst)
      t
    (if (atom (car alst))
        nil
      (let ((symbol (caar alst))
            (val    (cdar alst))
            (rest   (cdr  alst)))
        (and (n32p symbol)
             (n32p val)
             (n32p-n32p-alistp rest))))))

(defun n32p-listp (lst)
  (if (atom lst)
      t
    (and (n32p (car lst))
         (n32p-listp (cdr lst)))))

(defun n32p-n32p-alist-list-keys (alst)
  (if (atom alst)
      nil
    (cons (caar alst)
          (n32p-n32p-alist-list-keys (cdr alst)))))

(defthm n32p-n32p-alist-list-keys-n32p-listp
  (implies (n32p-n32p-alistp alst)
           (n32p-listp (n32p-n32p-alist-list-keys alst))))

(defun rv32-mem-program-words-loadedp (program-instr rv32)
  ;; Given an alist of the form ( ... (addr . instr-value) ... ), this
  ;; predicate checks whether it's loaded into the rv32 memory.
  (declare (xargs :stobjs (rv32)
                  :guard (n32p-n32p-alistp program-instr)))
  (if (atom program-instr)
      t
    (let ((addr (caar program-instr))
          (val  (cdar program-instr))
          (rest (cdr  program-instr)))
      (and (equal (rm32 addr rv32) val)
           (rv32-mem-program-words-loadedp rest rv32)))))

