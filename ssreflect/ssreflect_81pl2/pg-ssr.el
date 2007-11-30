;; Customization of PG for ssreflect syntax
;; Assia Mahboubi 2007

(defcustom coq-user-tactics-db
   '(("have" "hv" "have # : #" t "have") 
     ("congr" "con" "congr #" t "congr")
     ("wlog" "wlog" "wlog : / #" t "wlog")
     ("without loss" "wilog" "without loss #" t "without loss")
     ("unlock" "unlock" "unlock #" t "unlock")
     ("suffices" "suffices" "suffices # : #" t "suffices")
     ("suff" "suff" "suff # : #" t "suff")) 
   "Extended list of tactics, includings ssr and user defined ones")


(defcustom coq-user-commands-db
  '(("Unset Strict Implicit" "unsti" nil t "Strict\\s-+Implicit")
    ("Prenex Implicits" "pi" "Prenex Implicits #" t "Prenex\\s-+Implicits")
)
   "Extended list of commands, includings ssr and user defined ones")

(defcustom coq-user-tacticals-db
  '(("last" "lst" nil t "last"))
  "Extended list of tacticals, includings ssr and user defined ones")

(defcustom coq-user-reserved-db
  '("is" "nosimpl" "of")
  "Extended list of keywords, includings ssr and user defined ones")

(defcustom coq-user-solve-tactics-db
  '(("done" nil "done" nil "done")
    )
   "Extended list of closing tactic(al)s, includings ssr and user defined ones")
