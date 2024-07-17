(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
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

;; ADDI
;; Note, sign-extends imm to 32-bits

(define rv32-ADDI ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (((unless (rv32p rv32))
	(!ms (list :instruction 'ADDI
		   :rv32p	nil)
	     rv32))
       ;; Get PC
       (PC (rip rv32))
       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'ADDI
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
		   :instruction 'ADD
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (n32+ rs1-val imm))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!rip (+ PC 4) rv32)))
      rv32))


;; SUB

(define rv32-SUBI ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (rip rv32))
       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'SUBI
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1 instr))
       (imm   (get-i-imm instr))
       (rd    (get-rd  instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'SUBI
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (n32- rs1-val imm))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!rip (+ PC 4) rv32)))
      rv32))


;;
;; XORI
;;

(defthm n12p-implies-n32p
  (implies (n12p x) (n32p x)))

;; Sign extends imm
(define rv32-XORI ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (rip rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'XORI
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1 instr))
       (imm   (logext 12 (get-i-imm instr)))
       (rd    (get-rd  instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'XORI
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (n32 (logxor rs1-val imm)))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!rip (+ PC 4) rv32)))
      rv32))

;;
;; ORI
;;
;; Sign extends imm
(define rv32-ORI ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (rip rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'ORI
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1 instr))
       (imm   (logext 12 (get-i-imm instr)))
       (rd    (get-rd  instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'ORI
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (n32 (logior rs1-val imm)))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!rip (+ PC 4) rv32)))
      rv32))


;;
;; ANDI
;;
;; Sign extends imm
(define rv32-ANDI ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (rip rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'ANDI
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1 instr))
       (imm   (logext 12 (get-i-imm instr)))
       (rd    (get-rd  instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'ANDI
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (n32 (logand rs1-val imm)))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!rip (+ PC 4) rv32)))
      rv32))

;;
;; Shift Left Logical Immediate
;;
(define rv32-SLLI ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (rip rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'SLLI
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1 instr))
       (imm   (n05 (get-i-imm instr)))
       (rd    (get-rd  instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'SLLI
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (n32 (ash rs1-val imm)))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!rip (+ PC 4) rv32)))
      rv32))


;;
;; Shift Right Logical Immediate
;;
(define rv32-SRLI ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (rip rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'SRLI
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1 instr))
       (imm   (n05 (get-i-imm instr)))
       (rd    (get-rd  instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'SRLI
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (n32 (ash rs1-val (- imm))))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!rip (+ PC 4) rv32)))
      rv32))



;;
;; Shift Right Arithmetic Immediate

(define rv32-SRAI ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (rip rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'SRAI
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1 instr))
       (imm   (n05 (get-i-imm instr)))
       (rd    (get-rd  instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'SRAI
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (logext 32 (rgfi rs1 rv32)))
	
       ;; Compute result
       (result  (n32 (ash rs1-val (- imm))))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!rip (+ PC 4) rv32)))
      rv32))


;;
;; Set Less Than Immediate
;;
;; Sign extends imm
(define rv32-SLTI ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (rip rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'SLTI
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1 instr))
       (imm   (logext 12 (get-i-imm instr)))
       (rd    (get-rd  instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'SLTI
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (if (< rs1-val imm) 1 0))
	
       ;; Store result
       (rv32 (!rgfi rd result rv32))

       ;; Update PC
       (rv32 (!rip (+ PC 4) rv32)))
      rv32))

;;
;; Set Less Than Immediate Unsigned
;;
;; Sign extends imm but treats it as unsigned when comparing to rs1-val
(define rv32-SLTIU ((rv32 rv32p))
  :returns (rv32 rv32p :hyp :guard)
  (b* (;; Get PC
       (PC (rip rv32))

       ;; Memory probe
       ((if (< *2^32-5* PC))
	(!ms (list :at-location  PC
		   :instruction  'SLTIU
		   :memory-probe nil)
	     rv32))

       ;; Get instr
       (instr  (rm32 PC rv32))
       ;; Decode registers from instr
       (rs1   (get-rs1 instr))
       (imm   (n32 (logext 12 (get-i-imm instr))))
       (rd    (get-rd  instr))

       ;; x0 is hardwired 0, writes to it are discarded
       ;; but an exception must still be raised
       ;; See RISC-V ISA Spec, section 2.6
       ((unless (< 0 rd))
	(!ms (list :at-location PC
		   :instruction 'SLTIU
		   :destination-register-x0 t)
	     rv32))

       ;; Fetch values from registers
       (rs1-val (rgfi rs1 rv32))
	
       ;; Compute result
       (result  (if (< rs1-val imm) 1 0))
	
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



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ADDI Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ADDi constants
(defconst *addi-opcode* #b00010011)
(defconst *addi-funct3* #x0)

(define asm-addi ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *addi-funct3* 12)
            (ash (n05 rd)       7)
                 *addi-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *addi-funct3* 12)
           (ash rd             7)
           	*addi-opcode*   )))

(gl::def-gl-thm n32p-of-asm-addi-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *addi-funct3* 12)
                  (ash k    7)
                  *addi-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-addi
  (n32p (asm-addi rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-addi)
		  :use ((:instance n32p-of-asm-addi-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-addi-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *addi-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *addi-opcode* )
				    127)) 
		*addi-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-addi-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *addi-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *addi-opcode* ))
			
		*addi-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))


(gl::def-gl-thm get-i-imm-of-asm-addi-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *addi-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *addi-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-addi
  (equal (get-opcode (asm-addi i j k)) *addi-opcode*)
  :hints (("Goal" :in-theory (enable asm-addi)
                  :use ((:instance get-opcode-of-asm-addi-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-addi 
  (equal (get-funct3 (asm-addi i j k)) *addi-funct3*)
  :hints (("Goal" :in-theory (enable asm-addi)
                  :use ((:instance get-funct3-of-asm-addi-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-addi
  (equal (get-i-imm (asm-addi i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-addi)
                  :use ((:instance get-i-imm-of-asm-addi-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-addi-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *addi-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *addi-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-addi
  (equal (get-rs1 (asm-addi rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-addi)
		  :use ((:instance get-rs1-of-asm-addi-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-addi-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *addi-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *addi-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-addi
  (equal (get-rd (asm-addi rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-addi)
		  :use ((:instance get-rd-of-asm-addi-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; XORI Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; XORI constants
(defconst *xori-opcode* *addi-opcode*)
(defconst *xori-funct3* #x4)

(define asm-xori ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *xori-funct3* 12)
            (ash (n05 rd)       7)
                 *xori-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *xori-funct3* 12)
           (ash rd             7)
           	*xori-opcode*   )))

(gl::def-gl-thm n32p-of-asm-xori-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *xori-funct3* 12)
                  (ash k    7)
                  *xori-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-xori
  (n32p (asm-xori rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-xori)
		  :use ((:instance n32p-of-asm-xori-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-xori-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *xori-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *xori-opcode* )
				    127)) 
		*xori-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-xori-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *xori-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *xori-opcode* ))
			
		*xori-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))


(gl::def-gl-thm get-i-imm-of-asm-xori-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *xori-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *xori-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-xori
  (equal (get-opcode (asm-xori i j k)) *xori-opcode*)
  :hints (("Goal" :in-theory (enable asm-xori)
                  :use ((:instance get-opcode-of-asm-xori-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-xori 
  (equal (get-funct3 (asm-xori i j k)) *xori-funct3*)
  :hints (("Goal" :in-theory (enable asm-xori)
                  :use ((:instance get-funct3-of-asm-xori-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-xori
  (equal (get-i-imm (asm-xori i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-xori)
                  :use ((:instance get-i-imm-of-asm-xori-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-xori-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *xori-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *xori-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-xori
  (equal (get-rs1 (asm-xori rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-xori)
		  :use ((:instance get-rs1-of-asm-xori-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-xori-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *xori-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *xori-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-xori
  (equal (get-rd (asm-xori rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-xori)
		  :use ((:instance get-rd-of-asm-xori-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ORI Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; XORI constants
(defconst *ori-opcode* *addi-opcode*)
(defconst *ori-funct3* #x6)

(define asm-ori ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *ori-funct3* 12)
            (ash (n05 rd)       7)
                 *ori-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *ori-funct3* 12)
           (ash rd             7)
           	*ori-opcode*   )))

(gl::def-gl-thm n32p-of-asm-ori-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *ori-funct3* 12)
                  (ash k    7)
                  *ori-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-ori
  (n32p (asm-ori rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-ori)
		  :use ((:instance n32p-of-asm-ori-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-ori-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *ori-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *ori-opcode* )
				    127)) 
		*ori-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-ori-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *ori-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *ori-opcode* ))
			
		*ori-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))


(gl::def-gl-thm get-i-imm-of-asm-ori-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *ori-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *ori-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-ori
  (equal (get-opcode (asm-ori i j k)) *ori-opcode*)
  :hints (("Goal" :in-theory (enable asm-ori)
                  :use ((:instance get-opcode-of-asm-ori-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-ori 
  (equal (get-funct3 (asm-ori i j k)) *ori-funct3*)
  :hints (("Goal" :in-theory (enable asm-ori)
                  :use ((:instance get-funct3-of-asm-ori-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-ori
  (equal (get-i-imm (asm-ori i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-ori)
                  :use ((:instance get-i-imm-of-asm-ori-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-ori-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *ori-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *ori-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-ori
  (equal (get-rs1 (asm-ori rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-ori)
		  :use ((:instance get-rs1-of-asm-ori-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-ori-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *ori-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *ori-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-ori
  (equal (get-rd (asm-ori rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-ori)
		  :use ((:instance get-rd-of-asm-ori-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ANDI Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ANDI constants
(defconst *andi-opcode* *addi-opcode*)
(defconst *andi-funct3* #x7)

(define asm-andi ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *andi-funct3* 12)
            (ash (n05 rd)       7)
                 *andi-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *andi-funct3* 12)
           (ash rd             7)
           	*andi-opcode*   )))

(gl::def-gl-thm n32p-of-asm-andi-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *andi-funct3* 12)
                  (ash k    7)
                  *andi-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-andi
  (n32p (asm-andi rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-andi)
		  :use ((:instance n32p-of-asm-andi-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-andi-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *andi-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *andi-opcode* )
				    127)) 
		*andi-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-andi-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *andi-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *andi-opcode* ))
			
		*andi-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))


(gl::def-gl-thm get-i-imm-of-asm-andi-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *andi-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *andi-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-andi
  (equal (get-opcode (asm-andi i j k)) *andi-opcode*)
  :hints (("Goal" :in-theory (enable asm-andi)
                  :use ((:instance get-opcode-of-asm-andi-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-andi 
  (equal (get-funct3 (asm-andi i j k)) *andi-funct3*)
  :hints (("Goal" :in-theory (enable asm-andi)
                  :use ((:instance get-funct3-of-asm-andi-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-andi
  (equal (get-i-imm (asm-andi i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-andi)
                  :use ((:instance get-i-imm-of-asm-andi-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-andi-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *andi-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *andi-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-andi
  (equal (get-rs1 (asm-andi rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-andi)
		  :use ((:instance get-rs1-of-asm-andi-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-andi-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *andi-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *andi-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-andi
  (equal (get-rd (asm-andi rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-andi)
		  :use ((:instance get-rd-of-asm-andi-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; SLLI Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; SLLI constants
(defconst *slli-opcode* *addi-opcode*)
(defconst *slli-funct3* #x1)

(define asm-slli ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *slli-funct3* 12)
            (ash (n05 rd)       7)
                 *slli-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *slli-funct3* 12)
           (ash rd             7)
           	*slli-opcode*   )))

(gl::def-gl-thm n32p-of-asm-slli-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *slli-funct3* 12)
                  (ash k    7)
                  *slli-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-slli
  (n32p (asm-slli rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-slli)
		  :use ((:instance n32p-of-asm-slli-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-slli-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *slli-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *slli-opcode* )
				    127)) 
		*slli-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-slli-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *slli-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *slli-opcode* ))
			
		*slli-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))


(gl::def-gl-thm get-i-imm-of-asm-slli-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *slli-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *slli-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-slli
  (equal (get-opcode (asm-slli i j k)) *slli-opcode*)
  :hints (("Goal" :in-theory (enable asm-slli)
                  :use ((:instance get-opcode-of-asm-slli-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-slli 
  (equal (get-funct3 (asm-slli i j k)) *slli-funct3*)
  :hints (("Goal" :in-theory (enable asm-slli)
                  :use ((:instance get-funct3-of-asm-slli-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-slli
  (equal (get-i-imm (asm-slli i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-slli)
                  :use ((:instance get-i-imm-of-asm-slli-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-slli-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *slli-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *slli-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-slli
  (equal (get-rs1 (asm-slli rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-slli)
		  :use ((:instance get-rs1-of-asm-slli-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-slli-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *slli-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *slli-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-slli
  (equal (get-rd (asm-slli rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-slli)
		  :use ((:instance get-rd-of-asm-slli-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; SRLI Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; SRLI constants
(defconst *srli-opcode* *addi-opcode*)
(defconst *srli-funct3* #x5)
(defconst *srli-funct7* #x0)

(define asm-srli ((rs1 n05p) (imm n05p) (rd n05p))
 (mbe
  :logic (+ (ash (n05 imm)     20)
            (ash (n05 rs1)     15)
            (ash *srli-funct3* 12)
            (ash (n05 rd)       7)
                 *srli-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *srli-funct3* 12)
           (ash rd             7)
           	*srli-opcode*   )))

(gl::def-gl-thm n32p-of-asm-srli-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *srli-funct3* 12)
                  (ash k    7)
                  *srli-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-srli
  (n32p (asm-srli rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-srli)
		  :use ((:instance n32p-of-asm-srli-gl (i (n05 rs1)) (j (n05 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-srli-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *srli-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *srli-opcode* )
				    127)) 
		*srli-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-srli-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *srli-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *srli-opcode* ))
			
		*srli-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))


(gl::def-gl-thm get-i-imm-of-asm-srli-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *srli-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *srli-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-srli
  (equal (get-opcode (asm-srli i j k)) *srli-opcode*)
  :hints (("Goal" :in-theory (enable asm-srli)
                  :use ((:instance get-opcode-of-asm-srli-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-srli 
  (equal (get-funct3 (asm-srli i j k)) *srli-funct3*)
  :hints (("Goal" :in-theory (enable asm-srli)
                  :use ((:instance get-funct3-of-asm-srli-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-srli
  (equal (get-i-imm (asm-srli i j k)) (n05 j))
  :hints (("Goal" :in-theory (enable asm-srli)
                  :use ((:instance get-i-imm-of-asm-srli-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-srli-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *srli-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *srli-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-srli
  (equal (get-rs1 (asm-srli rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-srli)
		  :use ((:instance get-rs1-of-asm-srli-gl (i (n05 rs1)) (j (n05 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-srli-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *srli-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *srli-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-srli
  (equal (get-rd (asm-srli rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-srli)
		  :use ((:instance get-rd-of-asm-srli-gl (i (n05 rs1)) (j (n05 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-funct7-of-asm-srli-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct7 (+ (ash j 20)
			     (ash *srli-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *srli-opcode* ))
		*srli-funct7*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-funct7-of-asm-srli
  (equal (get-funct7 (asm-srli rs1 imm rd)) *srli-funct7*)
  :hints (("Goal" :in-theory (enable asm-srli)
		  :use ((:instance get-funct7-of-asm-srli-gl (i (n05 rs1)) (j (n05 imm)) (k (n05 rd)))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; SRAI Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; SRAI constants
(defconst *srai-opcode* *addi-opcode*)
(defconst *srai-funct3* #x5)
(defconst *srai-funct7* #x20)

(define asm-srai ((rs1 n05p) (imm n05p) (rd n05p))
 (mbe
  :logic (+ (ash *srai-funct7* 25) 
	    (ash (n05 imm)     20)
            (ash (n05 rs1)     15)
            (ash *srai-funct3* 12)
            (ash (n05 rd)       7)
                 *srai-opcode*   )
  :exec (+ (ash imm           20)
            (ash *srai-funct7* 25) 
           (ash rs1           15)
           (ash *srai-funct3* 12)
           (ash rd             7)
           	*srai-opcode*   )))

(gl::def-gl-thm n32p-of-asm-srai-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (n32p (+ (ash *srai-funct7* 25) 
		  (ash j    20)
                  (ash i    15)
                  (ash *srai-funct3* 12)
                  (ash k    7)
                  *srai-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-srai
  (n32p (asm-srai rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-srai)
		  :use ((:instance n32p-of-asm-srai-gl (i (n05 rs1)) (j (n05 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-srai-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash *srai-funct7* 25) 
					(ash j 20)
				       (ash *srai-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *srai-opcode* )
				    127)) 
		*srai-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-srai-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct3 (+  (ash *srai-funct7* 25) (ash j 20)
				       (ash *srai-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *srai-opcode* ))
			
		*srai-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))


(gl::def-gl-thm get-i-imm-of-asm-srai-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (n05 (get-i-imm  (+ (ash *srai-funct7* 25) 
			       (ash j 20)
				       (ash *srai-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *srai-opcode* )))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-srai
  (equal (get-opcode (asm-srai i j k)) *srai-opcode*)
  :hints (("Goal" :in-theory (enable asm-srai)
                  :use ((:instance get-opcode-of-asm-srai-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-srai 
  (equal (get-funct3 (asm-srai i j k)) *srai-funct3*)
  :hints (("Goal" :in-theory (enable asm-srai)
                  :use ((:instance get-funct3-of-asm-srai-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-srai
  (equal (n05 (get-i-imm (asm-srai i j k))) (n05 j))
  :hints (("Goal" :in-theory (enable asm-srai)
                  :use ((:instance get-i-imm-of-asm-srai-gl (i (n05 i)) (j (n05 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-srai-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash *srai-funct7* 25)
			     (ash j 20)
			     (ash *srai-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *srai-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-srai
  (equal (get-rs1 (asm-srai rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-srai)
		  :use ((:instance get-rs1-of-asm-srai-gl (i (n05 rs1)) (j (n05 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-srai-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-rd (+   (ash *srai-funct7* 25)
			     (ash j 20)
			     (ash *srai-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *srai-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-srai
  (equal (get-rd (asm-srai rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-srai)
		  :use ((:instance get-rd-of-asm-srai-gl (i (n05 rs1)) (j (n05 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-funct7-of-asm-srai-gl
  :hyp (and (n05p i) (n05p j) (n05p k))
  :concl (equal (get-funct7 (+ (ash *srai-funct7* 25)
				(ash j 20)
			     (ash *srai-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *srai-opcode* ))
		*srai-funct7*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-funct7-of-asm-srai
  (equal (get-funct7 (asm-srai rs1 imm rd)) *srai-funct7*)
  :hints (("Goal" :in-theory (enable asm-srai)
		  :use ((:instance get-funct7-of-asm-srai-gl (i (n05 rs1)) (j (n05 imm)) (k (n05 rd)))))))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; SLTI Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; SLTI constants
(defconst *slti-opcode* *addi-opcode*)
(defconst *slti-funct3* #x2)

(define asm-slti ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *slti-funct3* 12)
            (ash (n05 rd)       7)
                 *slti-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *slti-funct3* 12)
           (ash rd             7)
           	*slti-opcode*   )))

(gl::def-gl-thm n32p-of-asm-slti-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *slti-funct3* 12)
                  (ash k    7)
                  *slti-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-slti
  (n32p (asm-slti rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-slti)
		  :use ((:instance n32p-of-asm-slti-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-slti-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *slti-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *slti-opcode* )
				    127)) 
		*slti-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-slti-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *slti-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *slti-opcode* ))
			
		*slti-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))


(gl::def-gl-thm get-i-imm-of-asm-slti-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *slti-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *slti-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-slti
  (equal (get-opcode (asm-slti i j k)) *slti-opcode*)
  :hints (("Goal" :in-theory (enable asm-slti)
                  :use ((:instance get-opcode-of-asm-slti-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-slti 
  (equal (get-funct3 (asm-slti i j k)) *slti-funct3*)
  :hints (("Goal" :in-theory (enable asm-slti)
                  :use ((:instance get-funct3-of-asm-slti-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-slti
  (equal (get-i-imm (asm-slti i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-slti)
                  :use ((:instance get-i-imm-of-asm-slti-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-slti-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *slti-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *slti-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-slti
  (equal (get-rs1 (asm-slti rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-slti)
		  :use ((:instance get-rs1-of-asm-slti-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-slti-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *slti-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *slti-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-slti
  (equal (get-rd (asm-slti rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-slti)
		  :use ((:instance get-rd-of-asm-slti-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; SLTIU Assembler & Theorems ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; SLTIU constants
(defconst *sltiu-opcode* *addi-opcode*)
(defconst *sltiu-funct3* #x3)

(define asm-sltiu ((rs1 n05p) (imm n12p) (rd n05p))
 (mbe
  :logic (+ (ash (n12 imm)     20)
            (ash (n05 rs1)     15)
            (ash *sltiu-funct3* 12)
            (ash (n05 rd)       7)
                 *sltiu-opcode*   )
  :exec (+ (ash imm           20)
           (ash rs1           15)
           (ash *sltiu-funct3* 12)
           (ash rd             7)
           	*sltiu-opcode*   )))

(gl::def-gl-thm n32p-of-asm-sltiu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (n32p (+ (ash j    20)
                  (ash i    15)
                  (ash *sltiu-funct3* 12)
                  (ash k    7)
                  *sltiu-opcode*))
  :g-bindings (gl::auto-bindings (:nat j 12) (:mix (:nat i 5) (:nat k 5))))

(defthm n32p-of-asm-sltiu
  (n32p (asm-sltiu rs1 imm rd))
  :hints (("Goal" :in-theory (enable asm-sltiu)
		  :use ((:instance n32p-of-asm-sltiu-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-opcode-of-asm-sltiu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-opcode (logand (+ (ash j 20)
				       (ash *sltiu-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *sltiu-opcode* )
				    127)) 
		*sltiu-opcode*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(gl::def-gl-thm get-funct3-of-asm-sltiu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-funct3 (+ (ash j 20)
				       (ash *sltiu-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *sltiu-opcode* ))
			
		*sltiu-funct3*)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))


(gl::def-gl-thm get-i-imm-of-asm-sltiu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-i-imm  (+ (ash j 20)
				       (ash *sltiu-funct3* 12) 
				       (ash i 15) 
				       (ash k 7) 
				       *sltiu-opcode* ))
			
		j)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-opcode-of-asm-sltiu
  (equal (get-opcode (asm-sltiu i j k)) *sltiu-opcode*)
  :hints (("Goal" :in-theory (enable asm-sltiu)
                  :use ((:instance get-opcode-of-asm-sltiu-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-funct3-of-asm-sltiu 
  (equal (get-funct3 (asm-sltiu i j k)) *sltiu-funct3*)
  :hints (("Goal" :in-theory (enable asm-sltiu)
                  :use ((:instance get-funct3-of-asm-sltiu-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(defthm get-i-imm-of-asm-sltiu
  (equal (get-i-imm (asm-sltiu i j k)) (n12 j))
  :hints (("Goal" :in-theory (enable asm-sltiu)
                  :use ((:instance get-i-imm-of-asm-sltiu-gl (i (n05 i)) (j (n12 j)) (k (n05 k)))))))

(gl::def-gl-thm get-rs1-of-asm-sltiu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rs1  (+ (ash j 20)
			     (ash *sltiu-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *sltiu-opcode* ))
		i)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rs1-of-asm-sltiu
  (equal (get-rs1 (asm-sltiu rs1 imm rd)) (n05 rs1))
  :hints (("Goal" :in-theory (enable asm-sltiu)
		  :use ((:instance get-rs1-of-asm-sltiu-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))

(gl::def-gl-thm get-rd-of-asm-sltiu-gl
  :hyp (and (n05p i) (n12p j) (n05p k))
  :concl (equal (get-rd (+ (ash j 20)
			     (ash *sltiu-funct3* 12) 
			     (ash i 15) 
			     (ash k 7) 
			     *sltiu-opcode* ))
		k)
  :g-bindings (gl::auto-bindings (:nat i 5) (:nat j 12) (:nat k 5)))

(defthm get-rd-of-asm-sltiu
  (equal (get-rd (asm-sltiu rs1 imm rd)) (n05 rd))
  :hints (("Goal" :in-theory (enable asm-sltiu)
		  :use ((:instance get-rd-of-asm-sltiu-gl (i (n05 rs1)) (j (n12 imm)) (k (n05 rd)))))))


