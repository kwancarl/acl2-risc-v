(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
;(include-book "models/y86/y86-basic/common/operations" :dir :system)
(include-book "operations")
(include-book "rv-state")
(include-book "decode")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;					       ;;
;;    Integer Register-Immediate Operations    ;;
;;					       ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Format for RISC-V I-type operations
;;
;;   31                     20 19      15 14  12 11       7 6            0
;;  |-------------------------|----------|------|----------|--------------|
;;  |        imm[11:0]        |   rs1    |funct3|    rd    |    opcode    |
;;  |-------------------------|----------|------|----------|--------------|
;;            12 bits            5 bits   3 bits   5 bits       7 bits
;;	 I-immediate[11:0]        src1              dest          OP
;;

;; Load Byte
;; 
;;  ld = m[rs1 + imm][0:7]
;; 

(define rv32-LB ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (((unless (rv32p rv32))
	(!ms (list :instruction 'lb
		   :rv32p	nil)
	     rv32))
       ;; Get PC
       (PC (rip rv32))
       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'lb
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1   instr))
       (imm   (logext 12 (get-i-imm instr)))
       (rd    (get-rd    instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'LB
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (n32 (logext 8 (rm08 (n32+ rs1-val imm) rv32))))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!rip (+ PC 4) rv32)))
      rv32))

;; Load Half
;; 
;;  ld = m[rs1 + imm][0:15]
;; 
;; TODO: Is imm sign extended again?

(define rv32-LH ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (((unless (rv32p rv32))
	(!ms (list :instruction 'lb
		   :rv32p	nil)
	     rv32))
       ;; Get PC
       (PC (rip rv32))
       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'lb
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1   instr))
       (imm   (logext 12 (get-i-imm instr)))
       (rd    (get-rd    instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'LH
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (n32 (logext 16 (n16 (rm32 (n32+ rs1-val imm) rv32)))))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!rip (+ PC 4) rv32)))
      rv32))


;; Load Word
;; 
;;  ld = m[rs1 + imm][0:15]
;; 
;; TODO: Is imm sign extended again?

(define rv32-LW ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (((unless (rv32p rv32))
	(!ms (list :instruction 'lw
		   :rv32p	nil)
	     rv32))
       ;; Get PC
       (PC (rip rv32))
       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'lw
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1   instr))
       (imm   (logext 12 (get-i-imm instr)))
       (rd    (get-rd    instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'Lw
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (n32 (logext 32 (rm32 (n32+ rs1-val imm) rv32))))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!rip (+ PC 4) rv32)))
      rv32))


;;
;; Load Byte Unsigned
;; 
;;  ld = m[rs1 + imm][0:7]
;; 

(defthm n32p-of-n08p
  (implies (n08p x) (n32p x)))

(define rv32-LBU ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (((unless (rv32p rv32))
	(!ms (list :instruction 'lb
		   :rv32p	nil)
	     rv32))
       ;; Get PC
       (PC (rip rv32))
       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'lbu
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1   instr))
       (imm   (logext 12 (get-i-imm instr)))
       (rd    (get-rd    instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'LBU
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (rm08 (n32+ rs1-val imm) rv32))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!rip (+ PC 4) rv32)))
      rv32))


;;
;; Load Half Unsigned
;; 
;;  ld = m[rs1 + imm][0:16]
;; 

(defthm n32p-of-n08p
  (implies (n08p x) (n32p x)))

(define rv32-LHU ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (((unless (rv32p rv32))
	(!ms (list :instruction 'lhu
		   :rv32p	nil)
	     rv32))
       ;; Get PC
       (PC (rip rv32))
       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'lhu
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1   instr))
       (imm   (logext 12 (get-i-imm instr)))
       (rd    (get-rd    instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'LhU
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (n16 (rm32 (n32+ rs1-val imm) rv32)))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!rip (+ PC 4) rv32)))
      rv32))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;			   ;;
;;    Assembly Functions   ;;
;;			   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "centaur/gl/gl" :dir :system)

(gl::def-gl-thm n05-of-n05p
  :hyp (n05p x) 
  :concl (equal (n05 x) x)
  :g-bindings (gl::auto-bindings (:nat x 5)))
(gl::def-gl-thm n12-of-nl2
  :hyp (n12p x) 
  :concl (equal (n12 x) x)
  :g-bindings (gl::auto-bindings (:nat x 12)))

;(local (include-book "kestrel/bv-lists/bits-to-byte" :dir :system))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; LB Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; LB constants
(defconst *lb-opcode* #b11)
(defconst *lb-funct3* 0)

(define asm-lb ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *lb-funct3* 12)
            (ash (n05 rd)       7)
                 *lb-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *lb-funct3* 12)
           (ash rd             7)
           	*lb-opcode*   )))

(gl::def-gl-thm n32p-of-asm-lb-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *lb-funct3* 12)
                  (ash k    7)
                  *lb-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-lb
  (n32p (asm-lb rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-lb)
		  :use ((:instance n32p-of-asm-lb-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-lb-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *lb-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lb-opcode* )
				    127)) 
		*lb-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-lb-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *lb-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lb-opcode* ))
			
		*lb-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))


(gl::def-gl-thm get-i-imm-of-asm-lb-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *lb-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lb-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-lb
  (equal (get-opcode (asm-lb i j k)) *lb-opcode*)
  :hints (("Goal" :in-theory (enable asm-lb)
                  :use ((:instance get-opcode-of-asm-lb-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-lb 
  (equal (get-funct3 (asm-lb i j k)) *lb-funct3*)
  :hints (("Goal" :in-theory (enable asm-lb)
                  :use ((:instance get-funct3-of-asm-lb-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-lb
  (equal (get-i-imm (asm-lb i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-lb)
                  :use ((:instance get-i-imm-of-asm-lb-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-lb-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *lb-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *lb-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-lb
  (equal (get-rs1 (asm-lb rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-lb)
		  :use ((:instance get-rs1-of-asm-lb-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-lb-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *lb-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *lb-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-lb
  (equal (get-rd (asm-lb rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-lb)
		  :use ((:instance get-rd-of-asm-lb-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; LH Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; LH constants
(defconst *lh-opcode* #b11)
(defconst *lh-funct3* #x1)

(define asm-lh ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *lh-funct3* 12)
            (ash (n05 rd)       7)
                 *lh-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *lh-funct3* 12)
           (ash rd             7)
           	*lh-opcode*   )))

(gl::def-gl-thm n32p-of-asm-lh-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *lh-funct3* 12)
                  (ash k    7)
                  *lh-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-lh
  (n32p (asm-lh rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-lh)
		  :use ((:instance n32p-of-asm-lh-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-lh-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *lh-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lh-opcode* )
				    127)) 
		*lh-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-lh-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *lh-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lh-opcode* ))
			
		*lh-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))


(gl::def-gl-thm get-i-imm-of-asm-lh-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *lh-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lh-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-lh
  (equal (get-opcode (asm-lh i j k)) *lh-opcode*)
  :hints (("Goal" :in-theory (enable asm-lh)
                  :use ((:instance get-opcode-of-asm-lh-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-lh 
  (equal (get-funct3 (asm-lh i j k)) *lh-funct3*)
  :hints (("Goal" :in-theory (enable asm-lh)
                  :use ((:instance get-funct3-of-asm-lh-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-lh
  (equal (get-i-imm (asm-lh i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-lh)
                  :use ((:instance get-i-imm-of-asm-lh-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-lh-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *lh-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *lh-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-lh
  (equal (get-rs1 (asm-lh rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-lh)
		  :use ((:instance get-rs1-of-asm-lh-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-lh-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *lh-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *lh-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-lh
  (equal (get-rd (asm-lh rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-lh)
		  :use ((:instance get-rd-of-asm-lh-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; LW Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; LW constants
(defconst *lw-opcode* #b11)
(defconst *lw-funct3* #x2)

(define asm-lw ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *lw-funct3* 12)
            (ash (n05 rd)       7)
                 *lw-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *lw-funct3* 12)
           (ash rd             7)
           	*lw-opcode*   )))

(gl::def-gl-thm n32p-of-asm-lw-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *lw-funct3* 12)
                  (ash k    7)
                  *lw-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-lw
  (n32p (asm-lw rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-lw)
		  :use ((:instance n32p-of-asm-lw-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-lw-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *lw-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lw-opcode* )
				    127)) 
		*lw-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-lw-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *lw-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lw-opcode* ))
			
		*lw-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))


(gl::def-gl-thm get-i-imm-of-asm-lw-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *lw-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lw-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-lw
  (equal (get-opcode (asm-lw i j k)) *lw-opcode*)
  :hints (("Goal" :in-theory (enable asm-lw)
                  :use ((:instance get-opcode-of-asm-lw-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-lw 
  (equal (get-funct3 (asm-lw i j k)) *lw-funct3*)
  :hints (("Goal" :in-theory (enable asm-lw)
                  :use ((:instance get-funct3-of-asm-lw-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-lw
  (equal (get-i-imm (asm-lw i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-lw)
                  :use ((:instance get-i-imm-of-asm-lw-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-lw-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *lw-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *lw-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-lw
  (equal (get-rs1 (asm-lw rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-lw)
		  :use ((:instance get-rs1-of-asm-lw-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-lw-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *lw-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *lw-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-lw
  (equal (get-rd (asm-lw rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-lw)
		  :use ((:instance get-rd-of-asm-lw-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; LBU Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; LBU constants
(defconst *lbu-opcode* #b11)
(defconst *lbu-funct3* #x4)

(define asm-lbu ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *lbu-funct3* 12)
            (ash (n05 rd)       7)
                 *lbu-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *lbu-funct3* 12)
           (ash rd             7)
           	*lbu-opcode*   )))

(gl::def-gl-thm n32p-of-asm-lbu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *lbu-funct3* 12)
                  (ash k    7)
                  *lbu-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-lbu
  (n32p (asm-lbu rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-lbu)
		  :use ((:instance n32p-of-asm-lbu-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-lbu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *lbu-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lbu-opcode* )
				    127)) 
		*lbu-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-lbu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *lbu-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lbu-opcode* ))
			
		*lbu-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))


(gl::def-gl-thm get-i-imm-of-asm-lbu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *lbu-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lbu-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-lbu
  (equal (get-opcode (asm-lbu i j k)) *lbu-opcode*)
  :hints (("Goal" :in-theory (enable asm-lbu)
                  :use ((:instance get-opcode-of-asm-lbu-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-lbu 
  (equal (get-funct3 (asm-lbu i j k)) *lbu-funct3*)
  :hints (("Goal" :in-theory (enable asm-lbu)
                  :use ((:instance get-funct3-of-asm-lbu-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-lbu
  (equal (get-i-imm (asm-lbu i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-lbu)
                  :use ((:instance get-i-imm-of-asm-lbu-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-lbu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *lbu-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *lbu-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-lbu
  (equal (get-rs1 (asm-lbu rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-lbu)
		  :use ((:instance get-rs1-of-asm-lbu-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-lbu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *lbu-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *lbu-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-lbu
  (equal (get-rd (asm-lbu rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-lbu)
		  :use ((:instance get-rd-of-asm-lbu-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; LHU Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; LHU constants
(defconst *lhu-opcode* #b11)
(defconst *lhu-funct3* #x5)

(define asm-lhu ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *lhu-funct3* 12)
            (ash (n05 rd)       7)
                 *lhu-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *lhu-funct3* 12)
           (ash rd             7)
           	*lhu-opcode*   )))

(gl::def-gl-thm n32p-of-asm-lhu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *lhu-funct3* 12)
                  (ash k    7)
                  *lhu-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-lhu
  (n32p (asm-lhu rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-lhu)
		  :use ((:instance n32p-of-asm-lhu-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-lhu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *lhu-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lhu-opcode* )
				    127)) 
		*lhu-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-lhu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *lhu-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lhu-opcode* ))
			
		*lhu-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))


(gl::def-gl-thm get-i-imm-of-asm-lhu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *lhu-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *lhu-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-lhu
  (equal (get-opcode (asm-lhu i j k)) *lhu-opcode*)
  :hints (("Goal" :in-theory (enable asm-lhu)
                  :use ((:instance get-opcode-of-asm-lhu-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-lhu 
  (equal (get-funct3 (asm-lhu i j k)) *lhu-funct3*)
  :hints (("Goal" :in-theory (enable asm-lhu)
                  :use ((:instance get-funct3-of-asm-lhu-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-lhu
  (equal (get-i-imm (asm-lhu i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-lhu)
                  :use ((:instance get-i-imm-of-asm-lhu-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-lhu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *lhu-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *lhu-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-lhu
  (equal (get-rs1 (asm-lhu rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-lhu)
		  :use ((:instance get-rs1-of-asm-lhu-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-lhu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *lhu-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *lhu-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-lhu
  (equal (get-rd (asm-lhu rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-lhu)
		  :use ((:instance get-rd-of-asm-lhu-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))



