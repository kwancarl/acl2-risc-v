(in-package "ACL2")
(include-book "misc-events")
(include-book "operations")
(include-book "constants")


(defconst *rv32-reg-names* 
  `(:x0  :x1  :x2  :x3  :x4  :x5  :x6  :x7
    :x8  :x9  :x10 :x11 :x12 :x13 :x14 :x15 
    :x16 :x17 :x18 :x19 :x20 :x21 :x22 :x23 
    :x24 :x25 :x26 :x27 :x28 :x29 :x30 :x31))
(defconst *rv32-reg-names-len* (len *rv32-reg-names*))
;(defconst *2^32* (expt 2 20))

;; RISC-V machine state object
;; defstobj = define single-threaded object
(defstobj rv32
  ;; register file
  (rgf :type (array (unsigned-byte 32)      
		    (*rv32-reg-names-len*))
       :initially 0
       :resizable nil)
  ;; PC register
  (rip :type (unsigned-byte 32) :initially 0)

  ;; 2^xlen bytes of memory
  (mem :type (array (unsigned-byte 8) (*2^32*)) :initially 0 :resizable nil)

  ;; "Model state" used for debugging
  (ms  :type t :initially nil)
  :inline t
  :renaming
  ((update-rgfi !rgfi)
   (update-rip  !rip)
   (update-memi !memi)
   (update-ms   !ms)))


(defun stobj-raw-defs (form state)
  (declare (xargs :mode :program :stobjs (state)))
  (let* ((name (cadr form))
         (args (cddr form))
         (wrld (w state))
         (template (defstobj-template name args wrld)))
    (defstobj-raw-defs name template nil wrld)))

; Lemmas to help with proofs about STOBJs that hold X86 state.  Our
; goal is to prove a nice set of forward-chaining lemmas, as our
; predicates seem nicely set up for that.

(in-theory (disable nth))  ; Because NTH used to select object from
                           ; the rv32 state.

; We first deal with the STOBJ read lemmas

; RGF read lemmas

(defthm natp-nth-of-rgf
  ;; Read the register file.
  (implies (and (rgfp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (natp (nth i x)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm nth-of-rgf-<-2^32
  ;; Contents of register are in range [0..2^32-1].
  (implies (and (rgfp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (and (<= 0 (nth i x))
                (< (nth i x) (expt 2 32))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm natp-rgfi
  ;; Contents of register are nat.
  (implies (and (force (rv32p rv32))
                (force (n05p i)))
           (natp (rgfi i rv32)))
  :rule-classes :type-prescription)


(defthm rgfi-less-than-expt-2-32
  ;; Contents of register are in range [0..2^32-1].
  ;; >> Allows i = 15. 
  (implies (and (rv32p rv32)
                (n05p i))
           (and (<= 0 (rgfi i rv32))
                (< (rgfi i rv32) (expt 2 32))))
  :rule-classes :linear)


; RIP read lemmas

(defthm natp-rip
  ;; RIP is a nat.
  (implies (force (rv32p rv32))
           (natp (rip rv32)))
  :rule-classes :type-prescription)

(defthm rip-less-than-expt-2-32
  ;; RIP is in range [0...2^32-1].
  (implies (rv32p rv32)
           (and (<= 0 (rip rv32))
                (< (rip rv32) (expt 2 32))))
  :rule-classes :linear)



; MEM read lemmas

(defthm nth-of-mem-<=-256
  ;; Contents of memory (bytes) are in range [0...255].
  (implies (and (memp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (and (<= 0 (nth i x))
                (< (nth i x) 256)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm natp-nth-of-mem
  ;; Contents of memory (bytes) are nats.
  (implies (and (memp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (natp (nth i x)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (nth)))))

(defthm natp-memi-when-n30p-addr
  ;; Elements of memory from state with 24-bit address
  ;; are nats.
  (implies (and (rv32p rv32)
                (n32p addr))
           (natp (memi addr rv32)))
  :hints (("Goal" :use ((:instance natp-nth-of-mem
				   (i addr)
				   (x (nth *memi* rv32))))))
  :rule-classes (:rewrite :type-prescription))

(defthm memi-less-than-expt-2-8
  ;; Elements of memory from state with 24-bit address
  ;; are in range [0...255].
  (implies (and (rv32p rv32)
                (n32p addr))
           (< (memi addr rv32) 256))
  :rule-classes :linear)

; We wonder if the two lemmas about UPDATE-xxx would be better as
; :FORWARD-CHAINING rules (or, as both :REWRITE and :FORWARD-CHAINING
; rules), using *MEM-SIZE-IN-BYTES* and *REG-SIZE-IN-DWRDS* in the
; hypotheses instead of LEN.

(defthm length-is-len-when-not-stringp
  ;; Length is messy because it requires splitting on the 
  ;; case of a string.  
  (implies (not (stringp x))
           (equal (length x)
                  (len x)))
  :hints (("Goal" :in-theory (e/d (length) ()))))

; RGF update lemmas

(defthm rgfp-update-nth
  ;; Update to a register with a 64-bit nat is still a register.
  (implies (and (rgfp x)
                (integerp i)
                (<= 0 i)
                (< i (len x))
                (n32p v))
           (rgfp (update-nth i v x))))

(defthm rv32p-update-rgfi-n05p
  ;; Update to a register from state with a 64-bit nat is still a register.
  (implies (and (rv32p rv32)
		;; >> This allows update to r15. 
                (n05p i)
                (n32p v))
           (rv32p (!rgfi i v rv32))))


; RIP update lemma

(defthm rv32p-update-rip
  ;; Updating the RIP with a 64-bit nat preserves a legal state.
  (implies (and (rv32p rv32)
                (n32p v))
           (rv32p (!rip v rv32))))


; Memory update lemmas

(defthm memp-update-nth
  ;; Updating a memory with an 8-bit nat preserves a legal
  ;; memory.
  (implies (and (memp x)
                (integerp i)
                (<= 0 i)
                (< i (len x))
                (n08p v))
           (memp (update-nth i v x))))

(defthm rv32p-update-memi-rv32p
  ;; Updating the y86 memory with an 8-bit nat preserves a legal
  ;; y86 state.
  (implies (and (force (rv32p rv32))
                (force (n32p i))
                (force (n08p v)))
           (rv32p (!memi i v rv32))))

; Model-State update lemma

(defthm rv32p-update-ms
  ;; If the state is legal, updating the status flag
  ;; with an arbitrary value preserves a legal state.
  (implies (force (rv32p rv32))
           (rv32p (!ms v rv32))))


; Some additional state lemmas.

;; >> The following is true only because *rfgi* is declared 
;;    to be an array of length 16.  But there are actually 
;;    only 15 registers.

(defthm len-rv32-rgf
  ;; The length of the register file is 16.
  (implies (rv32p rv32)
           (equal (len (nth *rgfi* rv32))
                  32)))

(defthm len-rv32-mem
  (implies (rv32p rv32)
           (equal (len (nth *memi* rv32))
                  *2^32*)))

(defthm rv32p-properties
  (implies (rv32p rv32)
           (and (true-listp rv32)
                (equal (len rv32) 4)
		;; The 0th component is the register file.
                (rgfp (nth 0 rv32))
                (equal (len (nth 0 rv32)) 32)

                (ripp (nth 1 rv32))
		;; The memory is the 2th component.
                (memp (nth 2 rv32))
                (equal (len (nth 2 rv32))
                       *2^32*)

		;; Status is the 3th component.
                (msp  (nth 3 rv32))
                ))
  :hints (("Goal" :in-theory (enable rv32p rgfp ripp memp msp)))
  :rule-classes :forward-chaining)

; Hopefully, we have proven all the facts we need about the rv32
; machine state.

(in-theory (disable rv32p
                    rgfp rgfi !rgfi
                    ripp rip  !rip
                    memp memi !memi
                    msp  ms   !ms))



; Read/Write memory routines

(defun rm08 (addr rv32)
  ;; Truncate address to 24 bits and access from state's memory.
  ;; Result is one byte.
  (declare (xargs :guard (n64p addr)
                  :stobjs (rv32)))
  (memi (n32 addr) rv32))

(defthm natp-rm08
  ;; Byte read is a natp.
  (implies (rv32p rv32)
           (natp (rm08 addr rv32)))
  :rule-classes :type-prescription)

(defthm bound-rm08
  ;; Byte read is in range [0...255].
  (implies (rv32p rv32)
           (and (<= 0 (rm08 addr rv32))
                (< (rm08 addr rv32) 256))))

(in-theory (disable rm08))

(defun wm08 (addr v rv32)
  ;; Write an 8-bit nat
  ;; to state's memory. 
  (declare (xargs :guard (and (n32p addr)
                              (n08p v))
                  :stobjs (rv32)))
  ;; >> Not sure why it's done this way.
  (prog2$
   nil ; (cw "Address: ~p0, Byte: ~p1~%" addr v)
   (!memi (n32 addr) v rv32)))

(defthm rv32p-wr08
  ;; Writing an 8-bit nat to memory preserves legal state.
  (implies (and (n08p v)
                (rv32p rv32))
           (rv32p (wm08 addr v rv32))))

(in-theory (disable wm08))


;; CK: adding rm 32
(defun rm32 (addr rv32)
  ;; Truncate address to 24 bits and access 4 consecutive bytes 
  ;; from state's memory. Assemble into 32-bit quantity in little
  ;; endian fashion.  Note that this allows wrap around, but that
  ;; will be precluded in the asm by constraints there.
  (declare (xargs :guard (n32p addr)
                  :stobjs (rv32)))
  (let* ((byte0 (memi (n32    addr) rv32))
         (byte1 (memi (n32+ 1 addr) rv32))
         (byte2 (memi (n32+ 2 addr) rv32))
         (byte3 (memi (n32+ 3 addr) rv32)))

    (n32 (logior byte0
                 (ash byte1 8)
                 (ash byte2 16)
                 (ash byte3 24)))))

(defthm natp-rm32
  ;; Reading a 32-bit quantity from memory yields
  ;; a 32-bit natp.
  (implies (rv32p rv32)
           (n32p (rm32 addr rv32)))
  :rule-classes :type-prescription)

(defthm bound-rm32
  ;; Reading a 64-bit quantity from memory yields
  ;; a value in range [0...2^32-1].
  (implies (rv32p rv32)
           (and (<= 0 (rm32 addr rv32))
                (< (rm32 addr rv32) (expt 2 32)))))


(defthmd rm32-from-successive-bytes
  ;; This should be useful when we know the actual values
  ;; stored at 8 successive bytes. 
  ;; I'm keeping it disabled because I don't want it firing
  ;; on every instance of rm64.
  ;; >> could I add a syntaxp hyp to this to restrict it to
  ;;    fire only when I have constants.
  (implies (and ;(rv32p rv32)
		(n32p      addr )
		(n32p (+ 1 addr))
		(n32p (+ 2 addr))
		(n32p (+ 3 addr))
		(equal (rm08      addr   rv32) n0)
		(equal (rm08 (+ 1 addr)  rv32) n1)
		(equal (rm08 (+ 2 addr)  rv32) n2)
		(equal (rm08 (+ 3 addr)  rv32) n3))
	   (equal (rm32 addr rv32)
		  (n32 (logior      n0
			       (ash n1 8)
			       (ash n2 16)
			       (ash n3 24)))))
  :hints (("Goal" :in-theory (enable rm08))))


(defthmd rm32-from-successive-bytes-corollary
  (IMPLIES (AND (n32p addr)
		(< addr *2^32-5*))
	   (EQUAL (RM32 addr rv32)
		  (N32 (LOGIOR (rm08 addr rv32)
			       (ASH (rm08 (+ 1 addr) rv32) 8)
			       (ASH (rm08 (+ 2 addr) rv32) 16)
			       (ASH (rm08 (+ 3 addr) rv32) 24)))))
  :hints (("Goal" :use (:instance rm32-from-successive-bytes
				  (n0 (rm08 addr rv32))
				  (n1 (rm08 (+ 1 addr) rv32))
				  (n2 (rm08 (+ 2 addr) rv32))
				  (n3 (rm08 (+ 3 addr) rv32))))))


(in-theory (disable rm32))


(defun rm64 (addr rv32)
  ;; Truncate address to 24 bits and access 8 consecutive bytes 
  ;; from state's memory. Assemble into 64-bit quantity in little
  ;; endian fashion.  Note that this allows wrap around, but that
  ;; will be precluded in the asm by constraints there.
  (declare (xargs :guard (n32p addr)
                  :stobjs (rv32)))
  (let* ((byte0 (memi (n32    addr) rv32))
         (byte1 (memi (n32+ 1 addr) rv32))
         (byte2 (memi (n32+ 2 addr) rv32))
         (byte3 (memi (n32+ 3 addr) rv32))
         (byte4 (memi (n32+ 4 addr) rv32))
         (byte5 (memi (n32+ 5 addr) rv32))
         (byte6 (memi (n32+ 6 addr) rv32))
         (byte7 (memi (n32+ 7 addr) rv32)))

    (n64 (logior byte0
                 (ash byte1 8)
                 (ash byte2 16)
                 (ash byte3 24)
                 (ash byte4 32)
                 (ash byte5 40)
                 (ash byte6 48)
                 (ash byte7 56)))))

(defthm natp-rm64
  ;; Reading a 64-bit quantity from memory yields
  ;; a 64-bit natp.
  (implies (rv32p rv32)
           (n64p (rm64 addr rv32)))
  :rule-classes :type-prescription)

(defthm bound-rm64
  ;; Reading a 64-bit quantity from memory yields
  ;; a value in range [0...2^64-1].
  (implies (rv32p rv32)
           (and (<= 0 (rm64 addr rv32))
                (< (rm64 addr rv32) 18446744073709551616))))

(in-theory (disable rm64))

; Update lemmas
;; >>> Many of these could probably be combined.

(defthm rgfi-!rgfi
  ;; Accessing a register after writing it returns the 
  ;; value written.
  (equal (rgfi i (!rgfi i v rv32))
         v)
  :hints (("Goal" :in-theory (enable rgfi !rgfi))))

(defthm rgfi-read-through-different-address-!rgfi
  ;; Writing register i doesn't change the value of register
  ;; j, if i != j.
  (implies (and (n05p i)
                (n05p j)
                (not (equal i j)))
           (equal (rgfi i (!rgfi j v rv32))
                  (rgfi i rv32)))
  :hints (("Goal" :in-theory (enable rgfi !rgfi))))

(defthm rip-!rip
  ;; Accessing RIP after writing it returns the value
  ;; written.
  (equal (rip (!rip v rv32))
         v)
  :hints (("Goal" :in-theory (enable rip !rip))))

(defthm memi-!memi
  ;; Accessing a memory location after writing it returns the value
  ;; written.
  (equal (memi i (!memi i v rv32))
         v)
  :hints (("Goal" :in-theory (enable memi !memi))))

;; BY: I moved these from read-over-write.lisp because they were the 
;;     only lemmas there that weren't redundant. 

(defthm memi-read-through-different-address-!memi
  ;; Read over write to a different memory address.
  (implies (and (n32p i)
                (n32p j); j is a 32-bit number
                (not (equal i j)))
           (equal (memi i (!memi j v rv32)) ;; reading from i after the write to j
                  (memi i rv32)))	    ;; is the same as reading from i before writing
  :hints (("Goal" :in-theory (enable memi !memi))))

;; BY: I was surprised that for many of these read over write
;;     types of lemmas, I don't need to know that I'm operating
;;     on a rv32p.

(defthm rm08-wm08
  ;; Read over write to a memory address in the state.
  (implies (and ;(rv32p rv32)
                (n32p i)
                (n08p v))
           (equal (rm08 i (wm08 i v rv32))
                  v))
  :hints (("Goal" :in-theory (enable rm08 wm08))))

;; BY: Miscellaneous other lemmas I found I needed about state:

(defthm ms-over-!ms
  (equal (ms (!ms v rv32)) v)
  :hints (("Goal" :in-theory (enable ms !ms))))

(defthm ms-over-!rip
  (equal (ms (!rip v rv32))
	 (ms rv32))
  :hints (("Goal" :in-theory (enable ms !rip))))

(defthm ms-over-!rgfi
  (equal (ms (!rgfi r v rv32))
	 (ms rv32))
  :hints (("Goal" :in-theory (enable ms !rgfi))))

(defthm rgfi-over-!rip
  (equal (rgfi r (!rip v rv32))
	 (rgfi r rv32))
  :hints (("Goal" :in-theory (enable rgfi !rip))))

(defthmd rm64-from-successive-bytes
  ;; This should be useful when we know the actual values
  ;; stored at 8 successive bytes. 
  ;; I'm keeping it disabled because I don't want it firing
  ;; on every instance of rm64.
  ;; >> could I add a syntaxp hyp to this to restrict it to
  ;;    fire only when I have constants.
  (implies (and ;(rv32p rv32)
		(n32p addr)
		(n32p (+ 1 addr))
		(n32p (+ 2 addr))
		(n32p (+ 3 addr))
		(n32p (+ 4 addr))
		(n32p (+ 5 addr))
		(n32p (+ 6 addr))
		(n32p (+ 7 addr))
		(equal (rm08 addr rv32) n0)
		(equal (rm08 (+ 1 addr)  rv32) n1)
		(equal (rm08 (+ 2 addr)  rv32) n2)
		(equal (rm08 (+ 3 addr)  rv32) n3)
		(equal (rm08 (+ 4 addr)  rv32) n4)
		(equal (rm08 (+ 5 addr)  rv32) n5)
		(equal (rm08 (+ 6 addr)  rv32) n6)
		(equal (rm08 (+ 7 addr)  rv32) n7))
	   (equal (rm64 addr rv32)
		  (n64 (logior n0
			       (ash n1 8)
			       (ash n2 16)
			       (ash n3 24)
			       (ash n4 32)
			       (ash n5 40)
			       (ash n6 48)
			       (ash n7 56)))))
  :hints (("Goal" :in-theory (enable rm64 rm08))))

(defthm memi-over-!ms
  (equal (memi addr (!ms val rv32))
	 (memi addr rv32))
  :hints (("Goal" :in-theory (enable memi !ms))))

(defthm rm64-over-!ms
  (equal (rm64 addr (!ms val rv32))
	 (rm64 addr rv32))
  :hints (("Goal" :in-theory (enable rm64))))

(defthm rm32-over-!ms
  (equal (rm32 addr (!ms val rv32))
	 (rm32 addr rv32))
  :hints (("Goal" :in-theory (enable rm32))))



(defthm memi-over-!rip
  ;; Access to memory is not disturbed by write to rip.
  (equal (memi addr (!rip v rv32))
	 (memi addr rv32))
  :hints (("Goal" :in-theory (enable memi !rip))))

(defthm rm64-over-!rip
  ;; Reading a qword from memory is not affected by 
  ;; changes to rip.
  (equal (rm64 addr (!rip v rv32))
	 (rm64 addr rv32))
  :hints (("Goal" :in-theory (enable rm64))))

(defthm rm32-over-!rip
  ;; Reading a qword from memory is not affected by 
  ;; changes to rip.
  (equal (rm32 addr (!rip v rv32))
	 (rm32 addr rv32))
  :hints (("Goal" :in-theory (enable rm32))))


(defthm memi-over-!rgfi
  ;; Access to memory is not disturbed by write to regs.
  (equal (memi addr (!rgfi reg v rv32))
	 (memi addr rv32))
  :hints (("Goal" :in-theory (enable memi !rgfi))))

(defthm rm64-over-!rgfi
  ;; Reading a qword from memory is not affected by 
  ;; changes to regs.
  (equal (rm64 addr (!rgfi reg v rv32))
	 (rm64 addr rv32))
  :hints (("Goal" :in-theory (enable rm64))))

(defthm rm32-over-!rgfi
  ;; Reading a qword from memory is not affected by 
  ;; changes to regs.
  (equal (rm32 addr (!rgfi reg v rv32))
	 (rm32 addr rv32))
  :hints (("Goal" :in-theory (enable rm32))))



(defthm !rgfi-!rip-commute
  (equal (!rgfi r v1 (!rip v2 rv32))
	 (!rip v2 (!rgfi r v1 rv32)))
  :hints (("Goal" :in-theory (enable rv32p !rgfi !rip))))

(defthm !rip-over-!rip
  (equal (!rip v1 (!rip v2 rv32))
	 (!rip v1 rv32))
  :hints (("Goal" :in-theory (enable !rip rv32p))))

(defthm !rfgi-over-!rfgi
  (implies (and (reg-nump r1)
		(reg-nump r2))
	   (and (implies (equal r1 r2)
			 (equal (!rgfi r1 v1 (!rgfi r2 v2 rv32))
				(!rgfi r1 v1 rv32)))
		(implies (< r2 r1)
			 (equal (!rgfi r1 v1 (!rgfi r2 v2 rv32))
				(!rgfi r2 v2 (!rgfi r1 v1 rv32))))))
  :hints (("Goal" :in-theory (enable rv32p !rgfi))))

(defthm ms-over-!memi
  (equal (ms (!memi addr val rv32))
	 (ms rv32))
  :hints (("Goal" :in-theory (enable ms !memi))))

(defthm !memi-commutes-with-!rip
  (equal (!memi x v
		(!rip y rv32))
	 (!rip y (!memi x v rv32)))
  :hints (("Goal" :in-theory (enable !rip !memi))))

(defthm !memi-commutes-with-!rgfi
  (equal (!memi x v
		(!rgfi r y rv32))
	 (!rgfi r y (!memi x v rv32)))
  :hints (("Goal" :in-theory (enable !rgfi !memi))))

(defthm logand-lessp-24
   (implies (n32p n)
	    (equal (logand n *2^32-1*)
		   n))
   :hints (("Goal" :use (:instance logand-lessp (k 32)))))

(defthm rm08-over-!memi-different-address
  (implies (and ;(rv32p rv32)
		(n64p addr1)
		(n64p addr2)
		(not (equal (n32 addr1) (n32 addr2))))
	   (equal (rm08 addr1 (!memi addr2 v rv32))
		  (rm08 addr1 rv32)))
  :hints (("Goal" :in-theory (enable rm08 memi !memi))))

(defthm rm08-over-!rip
  (equal (rm08 addr (!rip v rv32))
	 (rm08 addr rv32))
  :hints (("Goal" :in-theory (enable rm08 !rip memi))))

(defthm rm08-over-!rgfi
  (equal (rm08 addr (!rgfi i v rv32))
	 (rm08 addr rv32))
  :hints (("Goal" :in-theory (enable rm08 !rgfi memi))))

(with-arithmetic-help-5
 (defthm logand-plus-crock1
   (implies (and (n64p i)
		 (posp x)
		 (posp y)
		 (< x 8)
		 (< y 8)
		 (not (equal x y)))
	    (not (equal (logand (+ x i) *2^24-1*)
			(logand (+ y i) *2^24-1*)))))
 (defthm logand-plus-crock2
   (implies (and (n64p i)
		 (posp x)
		 (< x 8))
	    (not (equal (logand (+ x i) *2^24-1*)
			(logand i *2^24-1*))))))

(with-arithmetic-help-5
 (defthm logand-n64p-with-self1
   (implies (n64p n)
	    (equal (logand n n)
		   n))))

(defthm rgfp-true-listp
  (implies (rgfp regs)
	   (true-listp regs))
  :hints (("Goal" :in-theory (enable rgfp))))

 (local (defthm update-nth-nth
	  (implies (and (true-listp l)
			(natp i)
			(< i (len l)))
		   (equal (update-nth i (nth i l) l)
			  l))
	  :hints (("Goal" :in-theory (enable nth)
		   :induct (nth i alst)))))
 (defthm !rgfi-over-rgfi-same-reg
   ;; >> I do need the first hyp for this one, but perhaps
   ;;    a weaker hyp would do.  Try true-listp.
   (implies (and (rv32p rv32)
		 (reg-nump i))
	    (equal (!rgfi i (rgfi i rv32) rv32)
		   rv32))
   :hints (("Goal" :in-theory (enable !rgfi rgfi rv32p)
		   :use ((:instance update-nth-nth (l (nth *rgfi* rv32)))))))

(defthmd rm64-from-successive-bytes-corollary
  (IMPLIES (AND (n32p addr)
		(< (+ 7 addr) *2^32-8*))
	   (EQUAL (RM64 addr rv32)
		  (N64 (LOGIOR (rm08 addr rv32)
			       (ASH (rm08 (+ 1 addr) rv32) 8)
			       (ASH (rm08 (+ 2 addr) rv32) 16)
			       (ASH (rm08 (+ 3 addr) rv32) 24)
			       (ASH (rm08 (+ 4 addr) rv32) 32)
			       (ASH (rm08 (+ 5 addr) rv32) 40)
			       (ASH (rm08 (+ 6 addr) rv32) 48)
			       (ASH (rm08 (+ 7 addr) rv32) 56)))))
  :hints (("Goal" :use (:instance rm64-from-successive-bytes
				  (n0 (rm08 addr rv32))
				  (n1 (rm08 (+ 1 addr) rv32))
				  (n2 (rm08 (+ 2 addr) rv32))
				  (n3 (rm08 (+ 3 addr) rv32))
				  (n4 (rm08 (+ 4 addr) rv32))
				  (n5 (rm08 (+ 5 addr) rv32))
				  (n6 (rm08 (+ 6 addr) rv32))
				  (n7 (rm08 (+ 7 addr) rv32))))))

(defthm rm08-over-!ms
  (equal (rm08 addr (!ms val rv32))
	 (rm08 addr rv32))
  :hints (("Goal" :in-theory (enable rm08 !ms memi))))


(defun wm32 (addr v rv32)
  ;; Given a 32-bit address, 32-bit value, and legal state,  extract 
  ;; the bytes from the value, write them
  ;; into memory at the next 8 addresses in little endian fashion. 
  ;; Note that this allows addresses to wrap, but that's precluded
  ;; in the asm by constraints there. 
  (declare (xargs :guard (and (n32p addr)
                              (n32p v))
                  :stobjs (rv32)))
  (let* ((addr0 (n32    addr))
         (addr1 (n32+ 1 addr))
         (addr2 (n32+ 2 addr))
         (addr3 (n32+ 3 addr))
	 ;
         (byte0 (n08      v     ))
         (byte1 (n08 (ash v  -8)))
         (byte2 (n08 (ash v -16)))
         (byte3 (n08 (ash v -24)))
	 ;
         (rv32 (!memi addr0 byte0 rv32))
         (rv32 (!memi addr1 byte1 rv32))
         (rv32 (!memi addr2 byte2 rv32))
         (rv32 (!memi addr3 byte3 rv32)))
    rv32))

(defthm rv32p-wm64
  ;; Writing a 64-bit nat to memory in the state, preserves
  ;; a legal state.
  (implies (and (n64p v)
                (rv32p rv32))
           (rv32p (wm32 addr v rv32))))

(in-theory (disable wm32))


