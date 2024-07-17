(in-package "ACL2")
(include-book "rv32i")

(defun init-rv32-state (status start-addr rv32)
 (declare (xargs :stobjs (rv32) :verify-guards nil))
 (let ((__function__ 'init-rv32-state))
   (declare (ignorable __function__))
   (b* ((rv32 (!ms status rv32))
        (rv32 (!rip (n32 start-addr) rv32)))
       rv32)))


