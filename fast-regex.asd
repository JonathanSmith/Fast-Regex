(in-package :asdf)
(defsystem #:fast-regex
    :version "0.0.1"
    :maintainer "Jonathan Smith"
    :licence "MIT/BSD"
    :description "DFA Base Regular Expressions"
    :serial t
    :components ((:file "package")
		 (:file "regex")))