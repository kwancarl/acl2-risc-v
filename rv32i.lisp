(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "operations")
(include-book "rv-state")
(include-book "imm-instr")
(include-book "r-type")
(include-book "ld-instr")
(include-book "st-instr")
(include-book "br-instr")
(include-book "u-imm-instr")
(include-book "j-instr")
(include-book "m-ext")

;;;;;;;;;;;;;;;;;;;;;;;;;
;;                     ;;
;;    Step Function    ;;
;;		       ;;
;;;;;;;;;;;;;;;;;;;;;;;;;

(define rv32-illegal-instr ((rv32 rv32p))
  ;; Report an illegal opcode in status flag.
    (b* ((pc (rip rv32))
         (byte-at-pc (rm08 pc rv32)))
        (!ms (list :illegal-opcode byte-at-pc
                   :at-location pc)
                   rv32)))

(local (include-book "kestrel/bv-lists/bits-to-byte" :DIR :SYSTEM ))
(local (include-book "kestrel/bv-lists/byte-to-bits" :DIR :SYSTEM ))
;(defconst *R-TYPE* (bits-to-byte (list 0 0 1 1 0 0 1 1)))
;(defconst *ADD-funct3* #x0)
;(defconst *ADD-funct7* #x0)

;; takes a machine state object
(define rv32-step ((rv32 rv32p))
  ;:returns (rv32-next rv32p :hyp :guard)
  (b* (;((unless (rv32p rv32))
       ; (!ms (list :not-rv32p t) rv32))

       ;; get the PC
       (PC     (rip rv32))
       ;; read the instruction from memory in machine object
       (instr  (rm32 PC rv32))
       (OP     (get-opcode instr))
       (funct3 (get-funct3 instr))
       (funct7 (get-funct7 instr)))
      (case OP
       ;; R-TYPE OPCODE 51 = #b0110011
       (#b0110011
	(case funct3
	 ;; ADD / SUB
	 (#x0
	  (case funct7
	   ;; ADD
	   (#x0  (rv32-add rv32))
	   ;; SUB
	   (#x20 (rv32-sub rv32))
	   (t 	 (!ms (list :bad-funct7 t) rv32))))
	 ;; XOR
	 (#x4 
          (case funct7
	   (#x00 (rv32-xor rv32))
	   ;; DIV
	   (#x01 (rv32-div rv32))
	   (t 	 (!ms (list :bad-funct7 t) rv32))))
	 ;; OR
	 (#x6 (rv32-or rv32))
	 ;; AND
	 ;; call the ACL2 function that peforms the "add"
	 (#x7 (rv32-and rv32))
	 (#x1 
	  (case funct7
	   ;; SLL
	   (#x00 (rv32-sll rv32))
	   ;; M EXTENSION
	   ;; DIV
	   (#x04 (rv32-div rv32))
	   (t 	 (!ms (list :bad-funct7 t) rv32))))
	 (#x5 
    	  (case funct7
	    ;; SRL / SRA
 	    (#x00 (rv32-srl rv32))
 	    (#x20 (rv32-sra rv32))
 	    ;; DIVU DIV UNSIGNED
 	    (#x01 (rv32-divu rv32))
	    (t 	 (!ms (list :bad-funct7 t) rv32))))
	 ;; SLT 
	 (#x2 (rv32-slt rv32))
	 ;; SLT (U)
	 (#x3 (rv32-sltu rv32))
	 (t (!ms (list :bad-funct3 t) rv32))))

       ;; Integer Immediate-Register Instructions
       (#b0010011
	(case funct3
	 (#x0 (rv32-addi rv32))
	 (#x4 (rv32-xori rv32))
	 (#x6 (rv32-ori  rv32))
	 (#x7 (rv32-andi rv32))
	 (#x1 (rv32-slli rv32))
 	 ;; SRLI / SRAI
	 (#x5 
    	  (case funct7
	    ;; SRLI
 	    (#x00 (rv32-srli rv32))
	    ;; SRAI TODO
 	    ;(#x20 (rv32-srai rv32))
	    (t 	 (!ms (list :bad-funct7 t) rv32))))
	 ;; SLTI
	 (#x2 (rv32-slti  rv32))
	 ;; SLTI (U)
	 (#x3 (rv32-sltiu rv32))
	 (t (!ms (list :bad-funct3 t) rv32))))

       ;; Load instructions
       (#b0000011
	(case funct3
	 ;; LB
	 (#x0 (rv32-lb  rv32))
	 ;; LH
	 (#x1 (rv32-lh  rv32))
	 ;; LW
	 (#x2 (rv32-lw  rv32))
	 ;; LBU
	 (#x4 (rv32-lbu rv32))
	 ;; LHU
	 (#x5 (rv32-lhu rv32))
	 (t (!ms (list :bad-funct3 t) rv32))))

       ;; Store instructions
       (#b0100011
	(case funct3
	 ;; SB
	 (#x0 (rv32-sb  rv32))
	 ;; SH
	 (#x1 (rv32-sh  rv32))
	 ;; SW
	 (#x2 (rv32-sw  rv32))
	 (t (!ms (list :bad-funct3 t) rv32))))

       ;; Branch instructions
       (#b1100011
	(case funct3
	 ;; BEQ
	 (#x0 (rv32-beq  rv32))
	 ;; Branch if not equal
	 (#x1 (rv32-bne  rv32))
	 ;; Branch if less than
	 (#x4 (rv32-blt  rv32))
	 ;; Branch if greater than or equal
	 (#x5 (rv32-bge  rv32))
	 ;; Branch if less than unsigned
	 (#x6 (rv32-bltu  rv32))
	 ;; Branch if greater than or equal unsigned
	 (#x7 (rv32-bgeu  rv32))
	 (t (!ms (list :bad-funct3 t) rv32))))

       ;; JAL Jump and Link
       (#b1101111 (rv32-jal rv32))

       ;; JALR Jump and Link Register
       (#b1100111 
	(case funct3
	 (#x0 (rv32-jalr rv32))
	 (t (!ms (list :bad-funct3 t) rv32))))

       ;; LUI Load Upper Imm
       (#b0110111 (rv32-lui rv32))

       ;; AUIPC Add Upper Imm to PC
       (#b0010111 (rv32-auipc rv32))

       (t (!ms (list :bad-op t :OP OP) rv32)))))


(defthm rv32-step-when-asm-add-rv-add
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-add i j k)))
	   (equal (rv32-step rv32) (rv32-add rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))


(defthm rv32-step-when-asm-add-full
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
		(not (equal (n05 k) 0))
		(equal (rm32 (rip rv32) rv32) (asm-add i j k)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) 4) 
		        (!rgfi (n05 k) 
		 	       (n32+ (rgfi (n05 i) rv32) (rgfi (n05 j) rv32))
		 	       rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-add rv32))
                  :in-theory (disable get-rs1 get-rs2 get-rd get-opcode get-funct3 get-funct7))))

(defthm asm-add-correctness
  (implies (and (rv32p rv32)
		(not (equal (n05 rd) 0))
		(natp (rip rv32))
		(< (rip rv32) *2^32-5*)
		(force (equal (rm32 (rip rv32) rv32) (asm-add rs1 rs2 rd))))
	   (equal (rgfi (n05 rd) (rv32-step rv32)) 
		  (n32+ (rgfi (n05 rs1) rv32) (rgfi (n05 rs2) rv32))))
  :hints (("goal" :expand ((rv32-step rv32)
		 	   (rv32-add  rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm rv32-step-when-asm-sub
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-sub i j k)))
	   (equal (rv32-step rv32) (rv32-sub rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm asm-add-correctness
  (implies (and (rv32p rv32)
		(not (equal (n05 rd) 0))
		(natp (rip rv32))
		(< (rip rv32) *2^32-5*)
		(force (equal (rm32 (rip rv32) rv32) (asm-add rs1 rs2 rd))))
	   (equal (rgfi (n05 rd) (rv32-step rv32)) 
		  (n32+ (rgfi (n05 rs1) rv32) (rgfi (n05 rs2) rv32))))
  :hints (("goal" :expand ((rv32-step rv32)
		 	   (rv32-add  rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))




(defthm rv32-step-when-asm-xor
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-xor i j k)))
	   (equal (rv32-step rv32) (rv32-xor rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm asm-xor-correctness
  (implies (and (rv32p rv32)
		(not (equal (n05 rd) 0))
		(natp (rip rv32))
		(< (rip rv32) *2^32-5*)
		(force (equal (rm32 (rip rv32) rv32) (asm-xor rs1 rs2 rd))))
	   (equal (rgfi (n05 rd) (rv32-step rv32)) 
		  (logxor (rgfi (n05 rs1) rv32) (rgfi (n05 rs2) rv32))))
  :hints (("goal" :expand ((rv32-step rv32)
		 	   (rv32-xor  rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))



(defthm rv32-step-when-asm-or-rv-or
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-or i j k)))
	   (equal (rv32-step rv32) (rv32-or rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))


(defthm rv32-step-when-asm-or-full
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
		(not (equal (n05 k) 0))
		(equal (rm32 (rip rv32) rv32) (asm-or i j k)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) 4) 
		        (!rgfi (n05 k) 
		 	       (logior (rgfi (n05 i) rv32) (rgfi (n05 j) rv32))
		 	       rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-or rv32))
                  :in-theory (disable get-rs1 get-rs2 get-rd get-opcode get-funct3 get-funct7))))

(defthm asm-or-correctness
  (implies (and (rv32p rv32)
		(not (equal (n05 rd) 0))
		(natp (rip rv32))
		(< (rip rv32) *2^32-5*)
		(force (equal (rm32 (rip rv32) rv32) (asm-or rs1 rs2 rd))))
	   (equal (rgfi (n05 rd) (rv32-step rv32)) 
		  (logior (rgfi (n05 rs1) rv32) (rgfi (n05 rs2) rv32))))
  :hints (("goal" :expand ((rv32-step rv32)
		 	   (rv32-or  rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))


(defthm rv32-step-when-asm-and-rv-and
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-and i j k)))
	   (equal (rv32-step rv32) (rv32-and rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))


(defthm rv32-step-when-asm-and-full
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
		(not (equal (n05 k) 0))
		(equal (rm32 (rip rv32) rv32) (asm-and i j k)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) 4) 
		        (!rgfi (n05 k) 
		 	       (logand (rgfi (n05 i) rv32) (rgfi (n05 j) rv32))
		 	       rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-and rv32))
                  :in-theory (disable get-rs1 get-rs2 get-rd get-opcode get-funct3 get-funct7))))

(defthm asm-and-correctness
  (implies (and (rv32p rv32)
		(not (equal (n05 rd) 0))
		(natp (rip rv32))
		(< (rip rv32) *2^32-5*)
		(equal (rm32 (rip rv32) rv32) (asm-and rs1 rs2 rd)))
	   (equal (rgfi (n05 rd) (rv32-step rv32)) 
		  (logand (rgfi (n05 rs1) rv32) (rgfi (n05 rs2) rv32))))
  :hints (("goal" :expand ((rv32-step rv32)
		 	   (rv32-and rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))


(defthm decode-asm-sll-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-sll i j k)))
	   (equal (rv32-step rv32) (rv32-sll rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-sll-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
		(not (equal (n05 k) 0))
		(equal (rm32 (rip rv32) rv32) (asm-sll i j k)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) 4) 
		        (!rgfi (n05 k) 
		 	       (n32 (ash (rgfi (n05 i) rv32) (n05 (rgfi (n05 j) rv32))))
		 	       rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-sll rv32))
                  :in-theory (disable get-rs1 get-rs2 get-rd get-opcode get-funct3 get-funct7))))

(defthm decode-asm-srl-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-srl i j k)))
	   (equal (rv32-step rv32) (rv32-srl rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-srl-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
		(not (equal (n05 k) 0))
		(equal (rm32 (rip rv32) rv32) (asm-srl i j k)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) 4) 
		        (!rgfi (n05 k) 
		 	       (n32 (ash (rgfi (n05 i) rv32) (- (n05 (rgfi (n05 j) rv32)))))
		 	       rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-srl rv32))
                  :in-theory (disable get-rs1 get-rs2 get-rd get-opcode get-funct3 get-funct7))))

(defthm decode-asm-sra-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-sra i j k)))
	   (equal (rv32-step rv32) (rv32-sra rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-sra-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
		(not (equal (n05 k) 0))
		(equal (rm32 (rip rv32) rv32) (asm-sra i j k)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) 4) 
		        (!rgfi (n05 k) 
		 	       (n32 (ash (logext 32 (rgfi (n05 i) rv32)) (- (n05 (rgfi (n05 j) rv32)))))
		 	       rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-sra rv32))
                  :in-theory (disable get-rs1 get-rs2 get-rd get-opcode get-funct3 get-funct7))))


(defthm decode-asm-slt-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-slt i j k)))
	   (equal (rv32-step rv32) (rv32-slt rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-slt-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
		(not (equal (n05 k) 0))
		(equal (rm32 (rip rv32) rv32) (asm-slt i j k)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) 4) 
		        (!rgfi (n05 k) 
		 	       (if (< (logext 32 (rgfi (n05 i) rv32))
				      (logext 32 (rgfi (n05 j) rv32)))
				   1 
				   0)
		 	       rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-slt rv32))
                  :in-theory (disable get-rs1 get-rs2 get-rd get-opcode get-funct3 get-funct7))))


(defthm decode-asm-sltu-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-sltu i j k)))
	   (equal (rv32-step rv32) (rv32-sltu rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-sltu-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
		(not (equal (n05 k) 0))
		(equal (rm32 (rip rv32) rv32) (asm-sltu i j k)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) 4) 
		        (!rgfi (n05 k) 
		 	       (if (< (rgfi (n05 i) rv32)
				      (rgfi (n05 j) rv32))
				   1 
				   0)
		 	       rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-sltu rv32))
                  :in-theory (disable get-rs1 get-rs2 get-rd get-opcode get-funct3 get-funct7))))




(defthm decode-asm-addi-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-addi rs1 imm rd)))
	   (equal (rv32-step rv32) (rv32-addi rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-addi-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
		(not (equal (n05 rd) 0))
		(equal (rm32 (rip rv32) rv32) (asm-addi rs1 imm rd)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) 4) 
		        (!rgfi (n05 rd) 
		 	       (n32+ (logext 12 (n12 imm)) (rgfi (n05 rs1) rv32))
		 	       rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-addi rv32))
                  :in-theory (disable get-rs1 get-i-imm get-rd get-opcode get-funct3 get-funct7))))



(defthm decode-asm-xori-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-xori rs1 imm rd)))
	   (equal (rv32-step rv32) (rv32-xori rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-xori-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
		(not (equal (n05 rd) 0))
		(equal (rm32 (rip rv32) rv32) (asm-xori rs1 imm rd)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) 4) 
		        (!rgfi (n05 rd) 
		 	       (n32 (logxor (rgfi (n05 rs1) rv32) (logext 12 (n12 imm))))
		 	       rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-xori rv32))
                  :in-theory (disable get-rs1 get-i-imm get-rd get-opcode get-funct3 get-funct7))))


(defthm decode-asm-ori-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-ori rs1 imm rd)))
	   (equal (rv32-step rv32) (rv32-ori rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-ori-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
		(not (equal (n05 rd) 0))
		(equal (rm32 (rip rv32) rv32) (asm-ori rs1 imm rd)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) 4) 
		        (!rgfi (n05 rd) 
		 	       (n32 (logior (rgfi (n05 rs1) rv32) (logext 12 (n12 imm))))
		 	       rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-ori rv32))
                  :in-theory (disable get-rs1 get-i-imm get-rd get-opcode get-funct3 get-funct7))))



(defthm decode-asm-andi-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-andi rs1 imm rd)))
	   (equal (rv32-step rv32) (rv32-andi rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-andi-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
		(not (equal (n05 rd) 0))
		(equal (rm32 (rip rv32) rv32) (asm-andi rs1 imm rd)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) 4) 
		        (!rgfi (n05 rd) 
		 	       (n32 (logand (rgfi (n05 rs1) rv32) (logext 12 (n12 imm))))
		 	       rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-andi rv32))
                  :in-theory (disable get-rs1 get-i-imm get-rd get-opcode get-funct3 get-funct7))))


(defthm decode-asm-slli-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-slli rs1 imm rd)))
	   (equal (rv32-step rv32) (rv32-slli rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))
(encapsulate
 nil
 (local (include-book "arithmetic-5/top" :dir :system))
 (local (include-book "ihs/logops-lemmas" :DIR :SYSTEM))
  (defthm n05-of-n12
    (equal (n05 (n12 x)) (n05 x))))

(defthm execute-asm-slli-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
		(not (equal (n05 rd) 0))
		(equal (rm32 (rip rv32) rv32) (asm-slli rs1 imm rd)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) 4) 
		        (!rgfi (n05 rd) 
		 	       (n32 (ash (rgfi (n05 rs1) rv32) (n05 imm)))
		 	       rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-slli rv32))
                  :in-theory (disable get-rs1 get-i-imm get-rd get-opcode get-funct3 get-funct7))))


(defthm decode-asm-srli-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-srli rs1 imm rd)))
	   (equal (rv32-step rv32) (rv32-srli rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-srli-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
		(not (equal (n05 rd) 0))
		(equal (rm32 (rip rv32) rv32) (asm-srli rs1 imm rd)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) 4) 
		        (!rgfi (n05 rd) 
		 	       (n32 (ash (rgfi (n05 rs1) rv32) (- (n05 imm))))
		 	       rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-srli rv32))
                  :in-theory (disable get-rs1 get-i-imm get-rd get-opcode get-funct3 get-funct7))))


(defthm decode-asm-slti-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-slti rs1 imm rd)))
	   (equal (rv32-step rv32) (rv32-slti rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-slti-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
		(not (equal (n05 rd) 0))
		(equal (rm32 (rip rv32) rv32) (asm-slti rs1 imm rd)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) 4) 
		        (!rgfi (n05 rd) 
		 	       (if (< (rgfi (n05 rs1) rv32) (logext 12 (n12 imm))) 1 0)
		 	       rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-slti rv32))
                  :in-theory (disable get-rs1 get-i-imm get-rd get-opcode get-funct3 get-funct7))))



(defthm decode-asm-sltiu-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-sltiu rs1 imm rd)))
	   (equal (rv32-step rv32) (rv32-sltiu rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-sltiu-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
		(not (equal (n05 rd) 0))
		(equal (rm32 (rip rv32) rv32) (asm-sltiu rs1 imm rd)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) 4) 
		        (!rgfi (n05 rd) 
		 	       (if (< (rgfi (n05 rs1) rv32) (n32 (logext 12 (n12 imm)))) 1 0)
		 	       rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-sltiu rv32))
                  :in-theory (disable get-rs1 get-i-imm get-rd get-opcode get-funct3 get-funct7))))


(defthm decode-asm-lb-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-lb rs1 imm rd)))
	   (equal (rv32-step rv32) (rv32-lb rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-lb-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
		(not (equal (n05 rd) 0))
		(equal (rm32 (rip rv32) rv32) (asm-lb rs1 imm rd)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) 4) 
		        (!rgfi (n05 rd) 
		 	       (n32 (logext 8 (rm08 (n32+ (rgfi (n05 rs1) rv32) (logext 12 (n12 imm))) rv32)))
		 	       rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-lb rv32))
                  :in-theory (disable get-rs1 get-i-imm get-rd get-opcode get-funct3 get-funct7))))


(defthm decode-asm-lh-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-lh rs1 imm rd)))
	   (equal (rv32-step rv32) (rv32-lh rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

;(local
;  (defthm lemma
;    (implies (and (equal (rm32 (rip rv32) rv32) (asm-lh rs1 imm rd))
;		  (force (equal (get-i-imm (asm-lh rs1 imm rd)) (n12 imm))))
;	     (equal (get-i-imm (rm32 (rip rv32) rv32))
;		    (n12 imm)))))

(defthm execute-asm-lh-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
		(not (equal (n05 rd) 0))
		(force (equal (rm32 (rip rv32) rv32) (asm-lh rs1 imm rd))))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) 4) 
		        (!rgfi (n05 rd) 
		 	       (n32 
				(logext 16
					(n16 
					 (rm32 (n32+ (rgfi (n05 rs1) rv32) 
						     (logext 12 (n12 imm))) 
						rv32))))
		 	       rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-lh rv32))
                  :in-theory (disable logext get-rs1 get-i-imm get-rd get-opcode get-funct3 get-funct7))))

(defthm decode-asm-lw-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-lw rs1 imm rd)))
	   (equal (rv32-step rv32) (rv32-lw rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-lw-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
		(not (equal (n05 rd) 0))
		(force (equal (rm32 (rip rv32) rv32) (asm-lw rs1 imm rd))))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) 4) 
		        (!rgfi (n05 rd) 
		 	       (n32 
				(logext 32
					 (rm32 (n32+ (rgfi (n05 rs1) rv32) 
						     (logext 12 (n12 imm))) 
						rv32)))
		 	       rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-lw rv32))
                  :in-theory (disable logext get-rs1 get-i-imm get-rd get-opcode get-funct3 get-funct7))))


(defthm decode-asm-lbu-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-lbu rs1 imm rd)))
	   (equal (rv32-step rv32) (rv32-lbu rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-lbu-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
		(not (equal (n05 rd) 0))
		(force (equal (rm32 (rip rv32) rv32) (asm-lbu rs1 imm rd))))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) 4) 
		        (!rgfi (n05 rd) 
			       (rm08 (n32+ (rgfi (n05 rs1) rv32) 
					   (logext 12 (n12 imm))) 
				     rv32)
		 	       rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-lbu rv32))
                  :in-theory (disable logext get-rs1 get-i-imm get-rd get-opcode get-funct3 get-funct7))))



(defthm decode-asm-lhu-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-lhu rs1 imm rd)))
	   (equal (rv32-step rv32) (rv32-lhu rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-lhu-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
		(not (equal (n05 rd) 0))
		(equal (rm32 (rip rv32) rv32) (asm-lhu rs1 imm rd)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) 4) 
		        (!rgfi (n05 rd) 
			       (n16 (rm32 (n32+ (rgfi (n05 rs1) rv32) 
					        (logext 12 (n12 imm))) 
				          rv32))
		 	       rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-lhu rv32))
                  :in-theory (disable logext get-rs1 get-i-imm get-rd get-opcode get-funct3 get-funct7))))


(defthm decode-asm-sb-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-sb rs1 rs2 imm)))
	   (equal (rv32-step rv32) (rv32-sb rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-sb-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
		(equal (rm32 (rip rv32) rv32) (asm-sb rs1 rs2 imm)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) 4) 
			(wm08 (n32+ (rgfi (n05 rs1) rv32)
			 	    (n12 imm))
			      (n08 (rgfi (n05 rs2) rv32))
			      rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-sb rv32))
                  :in-theory (disable logext get-rs1 get-rs2 get-s-imm get-rd get-opcode get-funct3 get-funct7))))



(defthm decode-asm-sh-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-sh rs1 rs2 imm)))
	   (equal (rv32-step rv32) (rv32-sh rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-sh-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
	        (n32p (1+ (n32+ (rgfi (n05 rs1) rv32) (n12 imm))))
		(equal (rm32 (rip rv32) rv32) (asm-sh rs1 rs2 imm)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) 4) 
			(wm08 (1+ (n32+ (rgfi (n05 rs1) rv32) (n12 imm)))
			      (n08 (rgfi (n05 rs2) rv32))
			      (wm08 (n32+ (rgfi (n05 rs1) rv32) (n12 imm))
				    (n08 (ash (rgfi (n05 rs2) rv32) -8))
				    rv32)))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-sh rv32))
                  :in-theory (disable logext get-rs1 get-rs2 get-s-imm get-rd get-opcode get-funct3 get-funct7))))



(defthm decode-asm-sw-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-sw rs1 rs2 imm)))
	   (equal (rv32-step rv32) (rv32-sw rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-sw-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
	        (n32p (1+ (n32+ (rgfi (n05 rs1) rv32) (n12 imm))))
	        (< (n32+ (rgfi (n05 rs1) rv32) (n12 imm)) *2^32-5*)
		(equal (rm32 (rip rv32) rv32) (asm-sw rs1 rs2 imm)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) 4) 
			(wm32 (n32+ (rgfi (n05 rs1) rv32) (n12 imm)) (rgfi (n05 rs2) rv32) rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-sw rv32))
                  :in-theory (disable logext get-rs1 get-rs2 get-s-imm get-rd get-opcode get-funct3 get-funct7))))



(defthm decode-asm-beq-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-beq rs1 rs2 imm)))
	   (equal (rv32-step rv32) (rv32-beq rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-beq-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
	        (n13p imm)
		(zerop (n01 imm))
		(n32p (+ (rip rv32) (logext 13 imm)))
		(equal (rm32 (rip rv32) rv32) (asm-beq rs1 rs2 imm)))
	   (equal (rv32-step rv32) 
		  (!rip (if (equal (rgfi (n05 rs1) rv32) (rgfi (n05 rs2) rv32))
			    (+ (rip rv32) (logext 13 imm) )
			    (+ (rip rv32) 4))
			rv32)))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-beq rv32))
                  :in-theory (disable logext get-rs1 get-rs2 get-s-imm get-rd get-opcode get-funct3 get-funct7))))


(defthm decode-asm-bne-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-bne rs1 rs2 imm)))
	   (equal (rv32-step rv32) (rv32-bne rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-bne-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
	        (n13p imm)
		(zerop (n01 imm))
		(n32p (+ (rip rv32) (logext 13 imm)))
		(equal (rm32 (rip rv32) rv32) (asm-bne rs1 rs2 imm)))
	   (equal (rv32-step rv32) 
		  (!rip (if (not (equal (rgfi (n05 rs1) rv32) (rgfi (n05 rs2) rv32)))
			    (+ (rip rv32) (logext 13 imm) )
			    (+ (rip rv32) 4))
			rv32)))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-bne rv32))
                  :in-theory (disable logext get-rs1 get-rs2 get-s-imm get-rd get-opcode get-funct3 get-funct7))))

(defthm decode-asm-blt-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-blt rs1 rs2 imm)))
	   (equal (rv32-step rv32) (rv32-blt rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-blt-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
	        (n13p imm)
		(zerop (n01 imm))
		(n32p (+ (rip rv32) (logext 13 imm)))
		(equal (rm32 (rip rv32) rv32) (asm-blt rs1 rs2 imm)))
	   (equal (rv32-step rv32) 
		  (!rip (if (< (logext 32 (rgfi (n05 rs1) rv32)) 
			       (logext 32 (rgfi (n05 rs2) rv32)))
			    (+ (rip rv32) (logext 13 imm) )
			    (+ (rip rv32) 4))
			rv32)))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-blt rv32))
                  :in-theory (disable logext get-rs1 get-rs2 get-s-imm get-rd get-opcode get-funct3 get-funct7))))


(defthm decode-asm-bge-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-bge rs1 rs2 imm)))
	   (equal (rv32-step rv32) (rv32-bge rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

;(defthm silly-rip-lemma
;  (implies (and (natp (rip rv32)) (< (rip rv32) *2^32-5*))
;	   (n32p (+ (rip rv32) 4))))

(defthm execute-asm-bge-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
	        (n13p imm)
		(zerop (n01 imm))
		(n32p (+ (rip rv32) (logext 13 imm)))
		(equal (rm32 (rip rv32) rv32) (asm-bge rs1 rs2 imm)))
	   (equal (rv32-step rv32) 
		  (!rip (if (>= (logext 32 (rgfi (n05 rs1) rv32)) 
				(logext 32 (rgfi (n05 rs2) rv32)))
			    (+ (rip rv32) (logext 13 imm) )
			    (+ (rip rv32) 4))
			rv32)))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-bge rv32))
                  :in-theory (disable logext get-rs1 get-rs2 get-s-imm get-rd get-opcode get-funct3 get-funct7))))

(defthm decode-asm-bltu-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-bltu rs1 rs2 imm)))
	   (equal (rv32-step rv32) (rv32-bltu rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))


(defthm execute-asm-bltu-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
	        (n13p imm)
		(zerop (n01 imm))
		(n32p (+ (rip rv32) (logext 13 imm)))
		(equal (rm32 (rip rv32) rv32) (asm-bltu rs1 rs2 imm)))
	   (equal (rv32-step rv32) 
		  (!rip (if (< (rgfi (n05 rs1) rv32) (rgfi (n05 rs2) rv32))
			    (+ (rip rv32) (logext 13 imm) )
			    (+ (rip rv32) 4))
			rv32)))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-bltu rv32))
                  :in-theory (disable logext get-rs1 get-rs2 get-s-imm get-rd get-opcode get-funct3 get-funct7))))

(defthm decode-asm-bgeu-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-bgeu rs1 rs2 imm)))
	   (equal (rv32-step rv32) (rv32-bgeu rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))


(defthm execute-asm-bgeu-correctness
  (implies (and (rv32p rv32)
		(< (rip rv32) *2^32-5*)
	        (n13p imm)
		(zerop (n01 imm))
		(n32p (+ (rip rv32) (logext 13 imm)))
		(equal (rm32 (rip rv32) rv32) (asm-bgeu rs1 rs2 imm)))
	   (equal (rv32-step rv32) 
		  (!rip (if (>= (rgfi (n05 rs1) rv32) (rgfi (n05 rs2) rv32))
			    (+ (rip rv32) (logext 13 imm) )
			    (+ (rip rv32) 4))
			rv32)))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-bgeu rv32))
                  :in-theory (disable logext get-rs1 get-rs2 get-s-imm get-rd get-opcode get-funct3 get-funct7))))


(defthm decode-asm-lui-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-lui imm rd)))
	   (equal (rv32-step rv32) (rv32-lui rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-lui-correctness
  (implies (and (rv32p rv32)
		(not (equal (n05 rd) 0))
		(< (rip rv32) *2^32-5*)
		(equal (rm32 (rip rv32) rv32) (asm-lui imm rd)))
	   (equal (rv32-step rv32) 
		  (!rip (+ 4 (rip rv32))
			(!rgfi (n05 rd) (ash (n20 imm) 12) rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-lui rv32)))))

(defthm decode-asm-auipc-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-auipc imm rd)))
	   (equal (rv32-step rv32) (rv32-auipc rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-auipc-correctness
  (implies (and (rv32p rv32)
		(not (equal (n05 rd) 0))
		(< (rip rv32) *2^32-5*)
		(equal (rm32 (rip rv32) rv32) (asm-auipc imm rd)))
	   (equal (rv32-step rv32) 
		  (!rip (+ 4 (rip rv32))
			(!rgfi (n05 rd) (n32+ (rip rv32) (logext 32 (ash (n20 imm) 12))) rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-auipc rv32)))))

(defthm decode-asm-jal-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-jal imm rd)))
	   (equal (rv32-step rv32) (rv32-jal rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-jal-correctness-1
  (implies (and (rv32p rv32)
		(not (equal (n05 rd) 0))
		(< (rip rv32) *2^32-5*)
		(equal (n01 imm) 0)
		(n21p imm)
		(n32p (+ (rip rv32) (logext 21 imm)))
		(equal (rm32 (rip rv32) rv32) (asm-jal imm rd)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) (logext 21 imm))
			(!rgfi (n05 rd) (n32+ (rip rv32) 4) rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-jal rv32)))))

(defthm execute-asm-jal-correctness-2
  (implies (and (rv32p rv32)
		(equal (n05 rd) 0)
		(< (rip rv32) *2^32-5*)
		(equal (n01 imm) 0)
		(n21p imm)
		(n32p (+ (rip rv32) (logext 21 imm)))
		(equal (rm32 (rip rv32) rv32) (asm-jal imm rd)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rip rv32) (logext 21 imm))
			rv32)))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-jal rv32)))))

(defthm decode-asm-jalr-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-jalr rs1 imm rd)))
	   (equal (rv32-step rv32) (rv32-jalr rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-jalr-correctness-1
  (implies (and (rv32p rv32)
		(not (equal (n05 rd) 0))
		(< (rip rv32) *2^32-5*)
		(equal (n01 imm) 0)
		(n32p (+ (rgfi (n05 rs1) rv32) (logext 12 (n12 imm))))
		(equal (rm32 (rip rv32) rv32) (asm-jalr rs1 imm rd)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rgfi (n05 rs1) rv32) (logext 12 (n12 imm)))
			(!rgfi (n05 rd) (n32+ (rip rv32) 4) rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-jalr rv32)))))

(defthm execute-asm-jalr-correctness-2
  (implies (and (rv32p rv32)
		(equal (n05 rd) 0)
		(< (rip rv32) *2^32-5*)
		(equal (n01 imm) 0)
		(n32p (+ (rgfi (n05 rs1) rv32) (logext 12 (n12 imm))))
		(equal (rm32 (rip rv32) rv32) (asm-jalr rs1 imm rd)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rgfi (n05 rs1) rv32) (logext 12 (n12 imm)))
			rv32)))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-jalr rv32)))))


(defthm execute-asm-jalr-correctness-1
  (implies (and (rv32p rv32)
		(not (equal (n05 rd) 0))
		(< (rip rv32) *2^32-5*)
		(equal (n01 imm) 0)
		(n32p (+ (rgfi (n05 rs1) rv32) (logext 12 (n12 imm))))
		(equal (rm32 (rip rv32) rv32) (asm-jalr rs1 imm rd)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rgfi (n05 rs1) rv32) (logext 12 (n12 imm)))
			(!rgfi (n05 rd) (n32+ (rip rv32) 4) rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-jalr rv32)))))

(defthm execute-asm-jalr-correctness-2
  (implies (and (rv32p rv32)
		(equal (n05 rd) 0)
		(< (rip rv32) *2^32-5*)
		(equal (n01 imm) 0)
		(n32p (+ (rgfi (n05 rs1) rv32) (logext 12 (n12 imm))))
		(equal (rm32 (rip rv32) rv32) (asm-jalr rs1 imm rd)))
	   (equal (rv32-step rv32) 
		  (!rip (+ (rgfi (n05 rs1) rv32) (logext 12 (n12 imm)))
			rv32)))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-jalr rv32)))))



;; M EXTENSION CORRECTNESS THEOREMS

(defthm decode-asm-div-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-div rs1 rs2 rd)))
	   (equal (rv32-step rv32) (rv32-div rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-div-correctness-nonzero
  (implies (and (rv32p rv32)
		(not (equal (n05 rd) 0))
		(not (equal (logext 32 (rgfi (n05 rs2) rv32)) 0))
		(< (rip rv32) *2^32-5*)
		(equal (rm32 (rip rv32) rv32) (asm-div rs1 rs2 rd)))
	   (equal (rv32-step rv32) 
		  (!rip (+ 4 (rip rv32))
			(!rgfi (n05 rd) 
			       (n32 (floor (logext 32 (rgfi (n05 rs1) rv32))
					   (logext 32 (rgfi (n05 rs2) rv32))))
			       rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-div rv32)))))

(defthm execute-asm-div-correctness-zero-1
  (implies (and (rv32p rv32)
		(not (equal (n05 rd) 0))
		(equal (logext 32 (rgfi (n05 rs2) rv32)) 0)
		(< (rip rv32) *2^32-5*)
		(equal (rm32 (rip rv32) rv32) (asm-div rs1 rs2 rd)))
	   (equal (rv32-step rv32) 
		  (!rip (+ 4 (rip rv32))
			(!rgfi (n05 rd) (n32 -1) rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-div rv32)))))


(defthm execute-asm-div-correctness-zero-2
  (implies (and (rv32p rv32)
		(not (equal (n05 rd) 0))
		(equal (rgfi (n05 rs2) rv32) 0)
		(< (rip rv32) *2^32-5*)
		(equal (rm32 (rip rv32) rv32) (asm-div rs1 rs2 rd)))
	   (equal (rv32-step rv32) 
		  (!rip (+ 4 (rip rv32))
			(!rgfi (n05 rd) (n32 -1) rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-div rv32)))))
;		  :use ((:instance logext-of-zero (n 32))))))






(defthm decode-asm-divu-correctness
  (implies (and (rv32p rv32)
		(equal (rm32 (rip rv32) rv32) (asm-divu rs1 rs2 rd)))
	   (equal (rv32-step rv32) (rv32-divu rv32)))
  :hints (("goal" :expand ((rv32-step rv32))
                  :in-theory (disable get-opcode get-funct3 get-funct7))))

(defthm execute-asm-divu-correctness-nonzero
  (implies (and (rv32p rv32)
		(not (equal (n05 rd) 0))
		(not (equal (rgfi (n05 rs2) rv32) 0))
		(< (rip rv32) *2^32-5*)
		(equal (rm32 (rip rv32) rv32) (asm-divu rs1 rs2 rd)))
	   (equal (rv32-step rv32) 
		  (!rip (+ 4 (rip rv32))
			(!rgfi (n05 rd) 
			       (n32 (floor (rgfi (n05 rs1) rv32)
					   (rgfi (n05 rs2) rv32)))
			       rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-divu rv32)))))

(defthm execute-asm-divu-correctness-zero
  (implies (and (rv32p rv32)
		(not (equal (n05 rd) 0))
		(equal (rgfi (n05 rs2) rv32) 0)
		(< (rip rv32) *2^32-5*)
		(equal (rm32 (rip rv32) rv32) (asm-divu rs1 rs2 rd)))
	   (equal (rv32-step rv32) 
		  (!rip (+ 4 (rip rv32))
			(!rgfi (n05 rd) (n32 -1) rv32))))
  :hints (("goal" :expand ((rv32-step rv32) (rv32-divu rv32)))))
