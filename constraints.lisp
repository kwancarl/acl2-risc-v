(include-book "std/util/define" :dir :system)
(include-book "ihs/basic-definitions" :DIR :SYSTEM)
(include-book "operations")

(define constr-eq-cond ((x integerp) (y integerp) (z integerp))
 (mbe :logic (equal (* x (- y z)) 0)
      :exec (zerop (* x (- y z)))))

;; Az * Bz = Cz

;; Flags / Jolt constraint inputs
;;
;; Bytecode_A, 	     RAM_A            ChunksX_0, // Should match rv_trace.to_circuit_flags()
;; // Bytecode_V        // Ram_V	      ChunksX_1, OpFlags_IsRs1Rs2,
;; Bytecode_ELFAddress, RS1_Read,        ChunksX_2, OpFlags_IsImm,
;; Bytecode_Bitflags,   RS2_Read,        ChunksX_3, OpFlags_IsLoad,
;; Bytecode_RS1,        RD_Read,                    OpFlags_IsStore,
;; Bytecode_RS2,        RAM_Read_Byte0,  ChunksY_0, OpFlags_IsJmp,
;; Bytecode_RD,         RAM_Read_Byte1,  ChunksY_1, OpFlags_IsBranch,
;; Bytecode_Imm,        RAM_Read_Byte2,  ChunksY_2, OpFlags_LookupOutToRd,
;;                      RAM_Read_Byte3,  ChunksY_3, OpFlags_SignImm,
;; LookupOutput,        RD_Write,                   OpFlags_IsConcat,                            
;;                      RAM_Write_Byte0, ChunksQ_0, OpFlags_IsVirtualSequence,
;;                      RAM_Write_Byte1, ChunksQ_1, OpFlags_IsVirtual,
;;                      RAM_Write_Byte2, ChunksQ_2,
;;                      RAM_Write_Byte3, ChunksQ_3,
;;                                                               
;;     // Instruction Flags
;;     // Should match JoltInstructionSet
;;     IF_Add,
;;     IF_Sub,
;;     IF_And,
;;     IF_Or,
;;     IF_Xor,
;;     IF_Lb,
;;     IF_Lh,
;;     IF_Sb,
;;     IF_Sh,
;;     IF_Sw,
;;     IF_Beq,
;;     IF_Bge,
;;     IF_Bgeu,
;;     IF_Bne,
;;     IF_Slt,
;;     IF_Sltu,
;;     IF_Sll,
;;     IF_Sra,
;;     IF_Srl,
;;     IF_Movsign,
;;     IF_Mul,
;;     IF_MulU,
;;     IF_MulHu,
;;     IF_Virt_Adv,
;;     IF_Virt_Assert_LTE,
;;     IF_Virt_Assert_LT_ABS,
;;     IF_Virt_Assert_EQ_SIGNS,
;; }



;; Flags are bitp, but (if 0 then else) returns then

;; x = x-flag ? (PC*4 + 0x800... -4) : rs1-val
;;               real-pc
(define x-val ((x-flg bitp) (pc n32p) (rs1-val n32p))
 :returns (val n32p)
 (if (= x-flg 1)
     (n32 pc) ;;(- (+ pc #x8) 4) ;; real pc?
     (n32 rs1-val)))
	  
;; y = y-flag ? imm : rs2-val
(define y-val ((y-flg bitp) (imm n32p) (rs2-val n32p))
 :returns (val n32p)
 (if (= y-flg 1)
     (n32 imm)
     (n32 rs2-val)))
	  
;; determines imm as signed int
(define imm-val ((sign-imm-flag bitp) (imm n32p))
 :returns (val integerp)
 (if (= sign-imm-flag 1)
     (logext 32 imm)
     (ifix imm)))

;; imm is signed here
(define load/store ((is-load bitp) 
		    (is-store bitp) 
		    (rs1-val n32p) 
		    (rs2-val n32p) 
		    (ram-a n32p) 
		    (mem-start-addr n32p))
 (mbe :logic (equal (* (+ is-load is-store) 
		       (+ rs1-val rs2-val (- ram-a) (- mem-start-addr))) 
		    0)
      :exec (zerop (* (+ is-load is-store) 
		      (+ rs1-val rs2-val (- ram-a) (- mem-start-addr))) )))


;; read/write constraint: 

;; "loop"
;;   (rw-constr is-load (read-byte 0) (write-byte 0))
;;   (rw-constr is-load (read-byte 1) (write-byte 1))
;;   (rw-constr is-load (read-byte 2) (write-byte 2))
;;   (rw-constr is-load (read-byte 3) (write-byte 3))
(define rw-constr ((is-load bitp) (read-byte n08p) (write-byte n08p))
 (mbe :logic (equal (* is-load (- read-byte write-byte)) 0)
      :exec  (zerop (* is-load (- read-byte write-byte)))))

(define rw-val-constr ((is-store bitp) (load-or-store-val n32p) (lookup-output n32p))
 (zerop (* is-store (- load-or-store-val lookup-output))))

;; Lookup constraints
(define is-add-constr ((is-add bitp) (lookup-query n32p) (x n32p) (y n32p))
 (zerop (* is-add (- lookup-query (+ x y)))))

;; need to check whether 2's complement is appropriate here
(define is-sub-constr ((is-sub bitp) (lookup-query n32p) (x n32p) (y n32p))
 (zerop (* is-sub (+ lookup-query (- x) y (- (expt 2 32))))))

(define is-load-constr ((is-load bitp) (lookup-query n32p) (load-or-store-val n32p))
 (zerop (* is-load (- lookup-query load-or-store-val))))

(define is-store-constr ((is-store bitp) (lookup-query n32p) (rs2-val n32p))
 (zerop (* is-store (- lookup-query rs2-val))))

;; (is-concat-isntr is-concat X X-chunks)
;; (is-concat-isntr is-concat Y Y-chunks)
;; TODO: determine type of chunks
(define is-concat-instr-constr ((is-concat-instr bitp) (val n32p) (chunks integerp)) 
 (constr-eq-cond is-concat-instr val chunks))

(define y-chunks-used ((is-shift bitp) chunk1 chunk2)
 (if (< 0 is-shift) chunk1 chunk2))

;; do for x / y chunks 0 ... C
(define is-concat-constr ((is-concat bitp) 
			  (lookup-chunks integerp) 
		   	  (y-chunks integerp)
			  (x-chunks integerp))
 (constr-eq-cond is-concat lookup-chunks (+ y-chunks (ash x-chunks 8))))


(define rd-update-constr ((rd n05p) 
			  (update-rd integerp) (rd-val n32p) (lookup-output n32p)) 
 (constr-eq-cond (* rd update-rd) rd-val lookup-output))

(define is-jump-constr ((rd n05p) (is-jump bitp) (pc-val n32p) (rd-val n32p))
 (constr-eq-cond (* rd is-jump) pc-val rd-val))

(define next-pc ((is-branch bitp) 
		 (lookup-out integerp) 
		 (pc-val n32p) 
		 (imm-val integerp)
		 (is-jump bitp))
 (if (< 0 (* is-branch lookup-out))
     (+ pc-val imm-val)
     (if (< 0 is-jump)
	 (+ lookup-out 4)
	 (+ pc-val 4))))

         
(define pc-constr ((pc n32p) (pc-val n32p) (next-pc n32p))
 (constr-eq-cond pc pc-val next-pc))


