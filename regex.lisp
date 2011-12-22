;;Jon Smith PCCRE IMPLEMENTATION
;;;
;;;05/20/2011... last updates.
;;;currently this is a 'textbook' regex->NFA->DFA construction.
;;;this ends up taking the DFA and producing a bunch of compiled code
;;;basically it can be a compiler from a regex string bunch of assembly
;;; shifts and jumps and comparisons

;;todo: find a way to do classes properly
;;      find a way to do things like lazy/greedy operators. 
;;      find a way to do anchoring properly
;;      find a way to do matches/submatches 
;;      (possibly by constructing a scanner within the DFA for each
;;      desired match and maintaining match-state.
;;      finish byte tests for default classes (digitp wordp, etc).
;#.(setf *efficiency-note-cost-threshold* 3)

(in-package :fast-regex)

(eval-when (:compile-toplevel :load-toplevel :execute) 
  (defvar epsilon '#:|epsilon|) 
;;epsilon transitions are special transitions within a nfa
;;they give the 'nodeterministic' aspect of it, meaning that
;; you can decide afterwards whether you wanted to take the
;; epsilon transition or not.

  (setf *print-circle* t)
;;the structures generated are circular, if we don't set print circular, we will
;;ruin our repl buffer as it will just print the structure forever

  (defstruct node
    (identity (gensym "Node"))
    (transitions nil )
    (is-final? T))
;;;basic node structure, we can use the same node type for both the DFA and the NFA.
;;;contains a gensym for identity, a list of transitions, and whether it is final.

  (defstruct transition
    (next-node nil)
    (value nil))
;;;a transition, placed in the transitions list.
;;;contains a next node, and a 

  (defparameter *byte-mode* nil)
;;;toggle for swithcing between an 8-bit byte input, and lisp 'character' input
;;;(normally unicode or ascii)
;;;(defvar *optimize-classes* t) not used

;;;(defvar *char-code-class-optimize-limit* 256) also not used

;;; the type for regex characters
;;; will either be an 8 bit byte-- or a lisp 'character' type
  (deftype regex-char () 
    (if *byte-mode* 
	'(unsigned-byte 8)
	'character))

;;;assuming that char-codes will either be
;;;unicode or ascii... kind of a big assumption
  (deftype regex-char-code ()
    (if *byte-mode*
	'(unsigned-byte 8)
	'(unsigned-byte 32)))

;;;recursively traverse from one node to the next (using transitions), eventually finding
;;;the final node in the chain. this could potentially overflow the stack, as it is not tail recursive.
;;;i have yet to see that, however.
  (defun get-final (nde)
    (let (seen-nodes)
      (labels ((seen-node? (node)
		 (member node seen-nodes))
	       (final-getter (node)
		 (push node seen-nodes)
		 (let ((final? (node-is-final? node)))
		   (if final?
		       (return-from get-final node)
		       (let ((transitions (node-transitions node)))
			 (dolist (trans transitions)
			   (unless (seen-node? (transition-next-node trans))
			     (final-getter (transition-next-node trans)))))))))
	(final-getter nde))))

;;;generate a link between an initial node and a final node, creating a transition with a value
  (defun %link-by-value (i f value)
    (push (make-transition :next-node f :value value) (node-transitions i))
    i)

;;;generate a link between an initial node and a final node using a chain of nodes
  (defun %link-by-chain (i f chain)
    (push (make-transition :next-node chain :value epsilon) (node-transitions i))
    (push (make-transition :next-node f :value epsilon) (node-transitions (get-final chain)))
    (setf (node-is-final? (get-final chain)) nil)
    i)

;;;a node, an epsilon transition followed by another node.
  (defun nop ()
    (node-chain epsilon))

;;;a a node, a value transition, followed by another node.
  (defun node-chain (value)
    (%link-by-value (make-node :is-final? nil) (make-node) value))

;;;concatenate operator, concatenates an initial and final node chain
;;;by concatenating the last node in the initial chain, to the first node
;;;in the final chain.
  (defun %concatenate-1 (i f)
    (let ((i-tail (get-final i)))
      (setf (node-is-final? i-tail) nil)
      (dolist (trans (node-transitions f))
	(push trans (node-transitions i-tail))))
    i)

;;;concatenate, via concatenate-1, generates code to concatenate a number of different
;;;nodes
  (defmacro %concatenate (&rest rest)
    (let ((i (reduce #'(lambda (x y) (cond ((not (and (or (node-p x) (listp x))
						      (or (node-p y) (listp y))))
					    `(nop))
					   ((not (or (node-p x) (listp x)))
					    `(%concatenate-1 (nop) ,y))
					   ((not (or (node-p y) (listp y)))
					    `(%concatenate-1 ,x (nop)))
					   (t
					    `(%concatenate-1 ,x ,y))))
		     rest)))
      i))

;;;the + operator
  (defmacro %one-or-more (&rest rest)
    `(%concatenate (%concatenate ,@rest) (%closure (%concatenate ,@rest))))
;;;the ? operator
  (defmacro %one-or-zero (&rest rest)
    `(%union2 (%concatenate ,@rest) (nop)))
;;;the{#,#} operator, sort of. will actuallly work for any list of numbers.
  (defmacro %n-closure (count-list form)
    `(%union2 ,@(mapcar (lambda (times &aux list)
			  (dotimes (i times)
			    (push form list))
			  (push '%concatenate list)) count-list)))

;;generate a character class out of a set of tokens, ex. could list all digits.
;;this seems inefficient, but if using a dfa, we can reduce ranges into simple range checks.
;;and even combine ranges that are placed toget (ex ([0-9]|[A-z]|[;-@]) would get reduced to a single range check
  (defmacro %char-class (&rest tokens)
    `(%union2 ,@(mapcar (lambda (token) `(node-chain ,(second token))) tokens)))

;;union (|) operator basically it takes a set of nodes and wraps them into
;;a single node with an NFA transition to itself... basically.
  (defun %union (&rest nodes)
    (let ((i (make-node :is-final? nil))
	  (f (make-node)))
      (dolist (node nodes)
	(push (make-transition :next-node node :value epsilon) (node-transitions i))
	(let ((final-n (get-final node)))
	  (setf (node-is-final? final-n) nil)
	  (push (make-transition :next-node f :value epsilon) (node-transitions final-n))))
      i))

;;a slight optimization on the union reduction.
;;basically, we can do a few reductions to eliminate some of the redundancy.
  (defmacro %union2 (&rest nodes)
    (let (NOTFOUND)
      (do ()
	  (NOTFOUND)
	(setf NOTFOUND t)
	(let (stack)
	  (mapcar #'(lambda (x) 
		      (cond ((and (listp x) (eq (first x) '%union2))
			     (setf NOTFOUND nil)
			     (dolist (rn (rest x))
			       (pushnew rn stack)))
			    ((and (listp x) (eq (first x) '%concatenate))
			     (when (rest x)
			       (pushnew x stack)))
			    (t (pushnew x stack))))
		  nodes)
	  (setf nodes (nreverse stack))))

      (setf nodes 
	    (let (filtered) 
	      (mapcar #'(lambda (x) 
			  (unless (symbolp x)
			    (push x filtered))) nodes)
	      (nreverse filtered)))
      `(%union ,@nodes)))

;;;kleene closure... the * operator.
;;;insert nops for empty closures.
  (defmacro %closure (s)
    (if (or (node-p s) (listp s))
	`(%closure-1 ,s)
	`(nop)))
    
;;;kleene closure, for real this time.
;;;you can see we are creating a node with a chain attached, and generating the proper
;;;epsilon transitions between:
;;; an initial node, and the start node, (so we can check the chain)
;;; an initial node, and the final node, (so we can skip the chain)
;;; a final node and the start node, (so we can check the chain again)
;;; a final node and the initial node, (so we can skip the chain)... i'm not sure if this is necessary.
  (defun %closure-1 (s)
    (let ((i (make-node :is-final? nil))
	  (f (make-node))
	  (final-s (get-final s)))
      (setf (node-is-final? final-s) nil)
      (push (make-transition :next-node s :value epsilon) (node-transitions i))
      (push (make-transition :next-node f :value epsilon) (node-transitions i))
      (push (make-transition :next-node s :value epsilon) (node-transitions final-s))
      (push (make-transition :next-node f :value epsilon)(node-transitions final-s))
      i))

;;;generates a range of characters based on char-code function.
  (defun chars-through (schar echar)
    (let ((schar-code (char-code schar))
	  (echar-code (char-code echar))
	  characters)
      (if (> echar-code schar-code)
	  (dotimes (i (+ (- echar-code schar-code) 1))
	    (push (code-char (+ i schar-code)) characters))
	  (dotimes (i (+ (- schar-code echar-code) 1))
	    (push (code-char (+ i echar-code)) characters)))
      (nreverse characters)))

;;;generates a set of transitions from one node to the next, based on a range of characters.
  (defun %through (c1 c2)
;;;If we do this using union + reduce, compilation gets very slow and produces exactly the same code...
    (let* ((i (make-node :is-final? nil))
	   (f (make-node))
	   (charset (chars-through c1 c2)))
      (dolist (char charset)
	(%link-by-value i f char))
      i))
		   
;;;hash table to contain our character tokens for tokenization part of parsing
  (defvar tokenhash (make-hash-table))

  (defun set-token (char val) (setf (gethash char tokenhash) val))
;;;set a character token to return a given :keyword, which we will dispatch on in parsing.

  (defun gettoken (char) (gethash char tokenhash :char))
;;;return either a the keyword for a dispatch character, or a keyword :char, indicating it is to be
;;;treated as a regular character

  (set-token  #\[ :lsquare)
  (set-token #\] :rsquare)
  (set-token #\\ :escape)
  (set-token #\| :union)
  (set-token #\$ :dollar)
  (set-token #\. :any)
  (set-token #\* :star)
  (set-token #\+ :plus)
  (set-token #\? :question)
  (set-token #\{ :lcurley)
  (set-token #\} :rcurley)
  (set-token #\- :dash)
  (set-token #\^ :carat)
  (set-token #\( :lparen)
  (set-token #\) :rparen)

  (defun tokenize (string)
    (map 'list #'(lambda (char) (list (gettoken char) char)) string))
;;;tokenizing is very easy.

  (defvar escapehash (make-hash-table))
;;;hashtable for escape characters, for dispatches as in ppcre...
;;;useful for newline as well as more advanced operators...

  (defun set-escape (char val) (setf (gethash char escapehash) val))
  (defun get-escape (char) (gethash char escapehash `(node-chain ,char)))
  ;;;setter and getter...

(set-escape #\t `(node-chain #\TAB))
(set-escape #\n `(node-chain #\NEWLINE))
(set-escape #\r `(node-chain #\RETURN))
(set-escape #\w `(%union2 (%through #\a #\z) (%through #\A #\Z))) ;;word
(set-escape #\W `(node-chain '!wordp)) ;;non-word
;(set-escape #\s `(node-chain 'whitep)) ;whitespace
(set-escape #\s `(%union2 (node-chain #\TAB) 
			  (node-chain #\NEWLINE)
			  (node-chain #\RETURN)
			  (node-chain #\SPACE)))
(set-escape #\S `(node-chain '!whitep)) ;;non-whitespace
;(set-escape #\d `(node-chain 'digitp)) ;;digit
(set-escape #\d `(%through #\0 #\9))
(set-escape #\D `(node-chain '!digitp)) ;;non-digit

#|(set-escape #\v (list))
(set-escape #\V (list))
(set-escape #\h (list))|#

;;;pretty much this is just basic parser.
;;;it is working in a loop, and constructing a tree as it goes.
;;;we always hold onto the top of the tree
;;;postfix operators are added onto the top
;;;infix operators force a rotation in the tree (by parsing the other half and becoming
;;;the top... no example of prefix operators that i can remember.
;;;parenthesis simulate a pushdown automata by using recursion. (infix ops kind of do this too).
;;;the parser generates transitions which when eval'd, generate the NFA DAG for the
;;;given regular expression.
  (defun parse (token-stream)
    (let ((tree (list '%concatenate))
	  (escape-mode nil))
      (flet ((parse-curley (list &aux 
				 (current nil)
				 (num-list nil))
	       (dolist (token list)
		 (if (eql (second token) #\,) 
		     (progn
		       (push (parse-integer (coerce current 'string)) num-list)
		       (setf current nil))
		     (push (second token) current)))
	       (when current
		 (push (parse-integer (coerce current 'string)) num-list))
			
	       num-list))

	(do* ((token (first token-stream) (first rest-tokens))
	      (rest-tokens (rest token-stream) (rest rest-tokens)))
	     ((not token))
	  (cond 
	    (escape-mode
	     (setf escape-mode nil)
	     (push (get-escape (second token)) tree))
	     
	    ((eq (first token) :char)
	     (push `(node-chain ,(second token)) tree))

	    ((eq (first token) :escape)
	     (setf escape-mode t))

	    ((eq (first token) :any)
	     (push `(node-chain 'any-char-p)  tree))

	    ((eq (first token) :star)
	     (setf (first tree) (list '%closure (first tree))))

	    ((eq (first token) :dollar)
	     (push '(node-chain #\NEWLINE) tree)) ;;;in strings, these are based on string position
	    ((eq (first token) :carat) ;;;i.e. a end or beginning of string
	     (push '(node-chain #\NEWLINE) tree)) ;;;here, we use newline instead.

	    ((eq (first token) :plus)
	     (setf (first tree) (list '%one-or-more (first tree))))

	    ((eq (first token) :question)
	     (setf (first tree) (list '%one-or-zero (first tree))))

	    ((eq (first token) :lcurley)
	     (let (lst)
	       (setf token (first rest-tokens))
	       (setf rest-tokens (rest rest-tokens))
	       (do ()
		   ((or (eql (first token) :rcurley) (not token)))
		 (push token lst)
		 (setf token (first rest-tokens))
		 (setf rest-tokens (rest rest-tokens)))

	       (setf (first tree) (list '%n-closure (parse-curley lst)  (first tree)))))

	    ((eq (first token) :union)
	     (setf tree (list (let ((rtree (parse rest-tokens)))
				(setf token nil)
				(setf rest-tokens nil)
				rtree)
			      (if (> (length tree) 2)
				  (reverse tree)
				  (first tree))
			      '%union2)))

	    ((eql (first token) :lparen)
	     (let (lst
		   (counter 1))
	       (do ()
		   ((= counter 0))
		 (setf token (first rest-tokens))
		 (setf rest-tokens (rest rest-tokens))
		 (cond ((eq (first token) :lparen)
			(push token lst)
			(incf counter))
		       ((and (eq (first token) :rparen) 
			     (> counter 1))
			(push token lst)
			(decf counter))
		       ((eq (first token) :rparen)
			(decf counter))
		       (t (push token lst))))
	       (push (parse (nreverse lst)) tree)))

	    ((eql (first token) :lsquare)
	     (let (lst)
	       (setf token (first rest-tokens))
	       (setf rest-tokens (rest rest-tokens))
	       (do ()
		   ((or (eql (first token) :rsquare) (not token)))
		 (push token lst)
		 (setf token (first rest-tokens))
		 (setf rest-tokens (rest rest-tokens)))
	       (setf lst (nreverse lst))
	       (push '%char-class lst)
	       (push lst tree))))))
      (nreverse tree)))

;;;basically, generate grammer, eval into NFA.
  (defun regexp-to-nfa (string)
    (let ((parse-tree (parse (tokenize string))))
      (unless (listp (first parse-tree))
	(eval parse-tree))))

;;;collect all of the states in an nfa tree
;;;given the start state recursively.
  (defun get-states (head)
    (let (states)
      (labels ((collect-state (state)
		 (unless (member state states :test 'eql)
		   (push state states)
		   (dolist (trans (node-transitions state))
		     (let ((next-node (transition-next-node trans)))
		       (collect-state next-node))))))
	(collect-state head)
	states)))

;;;difference here is
;;;we check to see if the transition value
;;;is equal to epsilon before collecting
;;;it into our list of states.
  (defun epsilon-closure (s)
    (let (nfa-states)
      (labels ((collect-state (nfa-state)
		 (unless (member nfa-state nfa-states)
		   (push nfa-state nfa-states)
		   (dolist (trans (node-transitions nfa-state))
		     (when (eq (transition-value trans) epsilon)
		       (let ((next-node (transition-next-node trans)))
			 (collect-state next-node)))))))
	(collect-state s))
      nfa-states))

;;;like above, but we are doing it for a set, only traversing
;;;each node once.
  (defun set-epsilon-closure (set)
    (let (nfa-states)
      (labels ((collect-state (nfa-state)
		 (unless (member nfa-state nfa-states)
		   (push nfa-state nfa-states)
		   (dolist (trans (node-transitions nfa-state))
		     (when (eq (transition-value trans) epsilon)
		       (let ((next-node (transition-next-node trans)))
			 (collect-state next-node)))))))
	(dolist (state set)
	  (collect-state state)))
      nfa-states))

;;;collect every transition that is not an
;;;epsilon transition of a group of states.
  (defun non-epsilon-transitions (states)
    (let (ne-ts)
      (dolist (s states)
	(dolist (trans (node-transitions s))
	  (unless (eq (transition-value trans) epsilon)
	    (push trans ne-ts))))
      ne-ts))

;;;if you remember computability and complexity, the next section
;;;is basically powerset construction. this is the slowest part
;;;of the entire compiler with the possibility of generating 2^n states
;;;for certain given NFAs. Most of the time it is fine, however.
;;;if you recall, we basically generate a table containing each of the
;;;potential epsilon closures of the NFA. Each of these closures will become
;;;a new state in the DFA.
(defun nfa-to-dfa-table (nfa)
    (declare (optimize (speed 3)))
    (let* (dfa-nodes-table)
      (labels ((get-closure-alist (transitions)
		 (let (closure-alist)
		   (dolist (net transitions)
		     (declare (type transition net))
		     (if (assoc (transition-value net) closure-alist)
			 (pushnew (transition-next-node net) (second (assoc (transition-value net) closure-alist)))
			 (pushnew (list (transition-value net)(list (transition-next-node net))) closure-alist)))
		   closure-alist))
	       (set-state-r (set)
		 (let* ((closure (set-epsilon-closure set))
			(net (non-epsilon-transitions closure))
			(closure-alist (get-closure-alist net)))
		   (when (and closure net closure-alist)
		     (dolist (ab closure-alist)
		       (let ((lis (list closure ab)))
			 (when (not (member lis dfa-nodes-table :test 'equal))
			   (push lis dfa-nodes-table)
			   (set-state-r (second ab))
			   )))))))
	(set-state-r (list nfa)))
      (reverse dfa-nodes-table)))

;;;we take our powerset table that we generated, and convert
;;;it back into a set of nodes, in the form of a DFA. This
;;;sub-optimal DFA can then go through the reduction phase,
;;;and we can produce an optimal DFA
  (defun make-dfa (dfa-nodes-table)
    (let ((dfahash (make-hash-table :test 'equal))
	  dfa-nodes)
      (dolist (node-spec dfa-nodes-table)
	(let* ((node-closure (first node-spec))
	       (value (first (second node-spec)))
	       (next-node-closure (set-epsilon-closure (second (second node-spec)))))
	  (push (create-dfa-node dfahash  node-closure value next-node-closure) dfa-nodes)))
      (dolist (dfa-node dfa-nodes)
	(resolve-closures dfahash dfa-node))
      (let ((rdfa (reverse dfa-nodes)))
	rdfa)))

;;;we take a list of the nodes (which are connected)
;;;within a DFA, and iteratively eliminating equivalent
;;;transitions, we are able to eliminate redundancy
;;;in the DFA
  (defun reduce-automaton (nodes-list)
    (let (used extras)
      (dolist (node nodes-list)
	(if (member node used :test #'nodes-equiv)
	    (unless (member node used :test #'equalp)
	      (pushnew node extras))
	    (pushnew node used)))
      (setf used (nreverse used))
      (setf extras (nreverse extras))
      (dolist (extra extras)
	(let (same)
	  (mapcar #'(lambda (x) 
		      (when (and (nodes-equiv x extra) (not (equalp x extra)))
			(setf same x)))
		  used)
	  (when same
	    (dolist (node nodes-list)
	      (dolist (trans (node-transitions node))
		(let ((ttnn (transition-next-node trans)))
		  (when (and ttnn (eql (node-identity extra) (node-identity ttnn)))
		    (setf (transition-next-node trans) same))))))))

      (first used)))
      
;;;basically we need to know if transition1 and transition2 are equivalent...
;;;that is, they have the same transition value and go between the same nodes.
  (defun trans-equiv (transition1 transition2)
    (declare 
     (optimize (speed 3))
     (type transition transition1)
     (type transition transition2))
    (let* ((t1nn (transition-next-node transition1))
	   (t2nn (transition-next-node transition2))
	   (t1nid (if (node-p t1nn) (node-identity t1nn)))
	   (t2nid (if (node-p t2nn) (node-identity t2nn))))
    
      (let ((result
	     (and (eql (transition-value transition1) (transition-value transition2))
		  (eql t1nid  t2nid))))
	result)))

;;;we can test the sets of transitions that we have collected, for differences.
  (defun transitions-equiv (transitions1 transitions2)
    (declare (optimize (speed 3)))
    (null (set-difference transitions1 transitions2 :test #'trans-equiv)))

;;two nodes are equivalent if their transitions are also equivalent
;;;and they are both the same type of 'state'.
 (defun nodes-equiv (node1 node2)
    (and 
     (eql (node-is-final? node1) (node-is-final? node2))
     (transitions-equiv (node-transitions node1) (node-transitions node2))))

;;;basically we have a hash table and a node.
;;;the hash table contains references to the reduced transitions  
(defun resolve-closures (dfa-hash dfa-node)
    (let ((transitions (node-transitions dfa-node))
	  new-transitions)
      (dolist (trans transitions)
	(if (transition-p trans)
	    (push trans new-transitions)
	    (push (make-transition :value (first trans) :next-node (gethash (second trans) dfa-hash)) new-transitions)))
      (when (eq new-transitions nil)
	(setf (node-is-final? dfa-node) t))
      (setf (node-transitions dfa-node) new-transitions))
    dfa-node)

;;;if anything in a closure contains a final state
;;;the entire closure is a final state.
  (defun closure-contains-final-state? (closure)
    (some #'node-is-final? closure))

  (defun create-dfa-node (dfahash node-closure value next-node-closure)
    (let ((node (or (gethash node-closure dfahash)
		    (let ((nde (make-node :is-final? (closure-contains-final-state? node-closure))))
		      (setf (gethash node-closure dfahash) nde)
		      nde))))
    
      (if (gethash next-node-closure dfahash)
	  (push (make-transition :next-node (gethash next-node-closure dfahash) :value value)
		(node-transitions node))
	  (push (list value next-node-closure) (node-transitions node)))
      node))


(eval-when (:compile-toplevel :load-toplevel :execute)
  (defmacro langfreq (language top-chars)
    (let ((code (gensym)))
      (let ((top-codes (map '(simple-array number (*)) #'char-code top-chars)))
	`(defun ,language  (,code)
	   (or (position ,code ,top-codes)
	       ,(+ (length top-codes) 1)))))))

(defun no-preference (char) (declare (ignore char)) 0) ;;always a tie.
(langfreq eng-freq "etaoin shrdlu")
(langfreq fr-freq "esait nrulo")
(langfreq sp-freq "eaosr nidlc")
(langfreq it-freq "eaion lrtsc")
(langfreq ger-freq "enisr atdhu")
(langfreq fasta #.(format nil "ATGCatgc~%BDHKMNRSVWY"))
(defvar *sort-language* #'no-preference)

;;;basically, the idea is that a given language will have a specific character
;;;frequency. this doesn't matter most of the time, but if you happen to know
;;;the language and the frequencies, it seems possible to sort your tests
;;;so that more frequent characters are tested first. This is kind of a proof of concept.
;;;It is not obvious that this sorting will produce actual results, given that
;;;we do a different optimization on 'ranges' of characters, so that tests such as :digit,
;;;can result in only two tests (we can simply check the rnage using GE and LE).
;;;it would be interesting to turn off range reductions and actually test this on.
;;;different types of text. (Does it give a boost?)
(defun sort-codes-by-frequency (codes &optional (language *sort-language*))
  (sort codes #'(lambda (x y) 
		  (cond ((and (listp x) (listp y))
			 (if (> (- (second x) (first x)) 
				(- (second y) (first y)))
			     x y))
			((listp x) x)
			((listp y) y)
			((symbolp x) x)
			((symbolp y) y)
			(t (< (funcall language x)
			      (funcall language y)))))))

;;;The other optimizations, which allows us to look at
;;;a set of char codes (normally the transitions of a DFA),
;;;and convert them into a list with 'min and max'
;;;this means that when checking a transition, we can simply
;;;check if it is within a 'range'... essentially replacing
;;;a multitude of machine instructions and jumps with fewer
(defun find-code-ranges (char-codes)
  (let (list min max)
    (setf char-codes (mapcan #'(lambda (x)
				 (if (symbolp x)
				     (progn (push x list)
					    nil)
				     (list x)))
			     char-codes))
    (setf char-codes (sort char-codes #'<))

    (map nil (lambda (code) 
	       (cond 
		 ((and (not min) (not max))
		  (setf min code)
		  (setf max code))
		 ((= (- code max) 1)
		  (setf max code))
		 ((= min max)
		  (push min list)
		  (setf min code)
		  (setf max code))
		 (t
		  (push (list min max) list)
		  (setf min code)
		  (setf max code)))) char-codes)
    (if (= min max)
	(push min list)
	(push (list min max) list))
    list))

(defvar transition-test-hash (make-hash-table))
(defmacro set-test (symbol fn-byte-symbol)
  `(%set-test ',symbol ',fn-byte-symbol))
(defun %set-test (symbol fn-byte-symbol)
  (setf (gethash symbol transition-test-hash) fn-byte-symbol))	

;;;needs to find ranges, and do tests via <= as well as =

;;;These are all done, basically because i can't think of how to
;;;implement 'not' on transitions. one possibility would be to have a
;;;specific flag on transitions, for 'not' transitions, and basically
;;;only allow not transitions to be combined with other not transtiions.
;;;being that we only would use not in character classes and here...
;;;I'm not sure it is worth it. (HAH!)

(set-test digitp b-digitp)
(set-test !digitp !b-digitp)

(defun b-digitp (number)
  (declare (type regex-char-code number))
  (>= 57 number 48))
(defun !b-digitp (number)
  (not (b-digitp number)))

(set-test alphap b-alphap)
(set-test !alphap !b-alphap)

(defun b-alphap (number)
  (declare (type regex-char-code number))
  (or (>= 122 number 97) (>= 90 number 65)))

(defun !b-alphap (number)
  (not (b-alphap number)))

(set-test wordp bwordp)
(set-test !wordp !bwordp)

(defun bwordp (number)
  (or (b-alphap number) (b-digitp number)))

(defun !bwordp (number)
  (not (bwordp number)))

(set-test whitep bwhitep)
(set-test !whitep !bwhitep)

(defun bwhitep (number)
  (declare (type regex-char-code number))
  (or (= number 10)
      (= number 9)
      (= number 13)
      (= number 32)))
(defun !bwhitep (number)
  (not (bwhitep number)))

(set-test any any-char-p)

(defun any-char-p (character)
  (declare (ignore character))
  t)


(declaim (inline digit-char-p b-digitp !digitp !b-digitp
		 alpha-char-p b-alphap !alphap !b-alphap
		 alphanumericp bwordp !wordp !bwordp
		 graphic-char-p !whitep !bwhitep
		 any-char-p))

;;;this is kind of the punchline.
;;;instead of actually traversing the dfa, it is possible
;;;to encode the DFA as machine code representing each state's transitions
;;;based on the current character... with each state having a tag and a 'jump'
;;;to or from it. It is actually pretty straightforward... despite transition generation
;;;and other parts of it seeming a little hairy.

  (defun compile-greedy-dfa (dfa)
    (let (dfa-states)
      (labels ((get-dfa-states (state)
		 (when state
		   (unless (member state dfa-states :test 'eql)
		     (push state dfa-states)
		     (let ((transitions (node-transitions state)))
		       (dolist (transition transitions)
			 (get-dfa-states (transition-next-node transition))))))))
	(get-dfa-states dfa)
	(setf dfa-states (nreverse dfa-states))

	(let* ((strlen (gensym "strlen"))
	       (string (gensym "string"))
	       (char (gensym "char"))
	       (char-code (gensym "char-code"))
	       (i (gensym "i"))
	       (ret (gensym "ret"))
	       symb-hash
	       (success-symb (gensym "success"))
	       (failure-symb (gensym "failure")))

	  (mapcar #'(lambda (node) 
		      (push (list node (gensym "node")) symb-hash)) dfa-states)
	  (let ((node-code 
		 (mapcan 
		  #'(lambda (node)
		      (let* ((node-symb (second (assoc node symb-hash)))
			     (final-state? (node-is-final? node))
			     (transitions (node-transitions node))
			     transitions-by-next-node)

			(map nil (lambda (trans)
				   (let ((goto
					  (second (assoc
						   (transition-next-node trans)
						   symb-hash))))
				     (if (not (assoc goto transitions-by-next-node))
					 (push (list 
						goto 
						(list 
						 (transition-value trans)))
					       transitions-by-next-node)
					 (push (transition-value trans)
					       (second 
						(assoc goto transitions-by-next-node))))))
			     transitions)

			(let ((trans-code 
			       (mapcar 
				(lambda (x)
				  (let* ((goto (first x))
					 (transition-values 
					  (sort-codes-by-frequency
					   (find-code-ranges
					    (mapcar
					     (lambda (x)
					       (if (characterp x)
						   (char-code x)
						   x))
					     (second x)))))
					 (conditionals 
					  (mapcar 
					   (lambda (val)
					     (cond ((listp val)
						    `(<= ,(first val)
							 ,char-code
							 ,(second val)))
						   ((numberp val)
						    `(= ,char-code ,val))
						   ((symbolp val)
						    `(,(gethash val transition-test-hash)
						       ,char-code))))
					   transition-values)))
				    `((or ,@conditionals)
				      ,(if goto 
					   (list 'go goto) 
					   (list 'go success-symb)))
				    ))
				transitions-by-next-node)))
				    
	     
			  `(,node-symb
			    ,@(list (list 'if (list '= i strlen)
					  (list 'go (if final-state? success-symb failure-symb))))
			    (setf ,char-code
				  ,(if *byte-mode*
				       `(aref ,string ,i)
				       `(char-code (aref ,string ,i))))
			    (incf ,i)
			    (cond 
			      ,@trans-code
			      ,(list 't (list 'go failure-symb))))
			  ))) dfa-states)))
	    `(function (lambda (,string &optional (,i 0) (,strlen (length ,string)))
	       (declare 
		(optimize (speed 3) (safety 0) (space 0) (debug 0))
		(type fixnum ,i ,strlen)
		(type (simple-array regex-char (*)) ,string))
	       (let* (,ret 
		      (,char (aref ,string ,i))
		      (,char-code ,(if *byte-mode* 
				       char
				       `(char-code ,char))))
		 (declare (type regex-char ,char)
			  (type regex-char-code ,char-code) 
			  (type (or t nil) ,ret))

		 (tagbody 
		    ,@node-code
		    ,success-symb
		    (setf ,ret t)
		    ,failure-symb)
		 (values ,ret ,i)))))))))

(defun compile-greedy-dfa2 (dfa)
  (let (dfa-states)
    (labels ((get-dfa-states (state)
	       (when state
		 (unless (member state dfa-states :test 'eql)
		   (push state dfa-states)
		   (let ((transitions (node-transitions state)))
		     (dolist (transition transitions)
		       (get-dfa-states (transition-next-node transition))))))))
      (get-dfa-states dfa)
      (setf dfa-states (nreverse dfa-states))

      (let* ((strlen (gensym "strlen"))
	     (string (gensym "string"))
	     (char (gensym "char"))
	     (char-code (gensym "char-code"))
	     (i (gensym "i"))
	     (farthest-match (gensym "farthest-match"))
	     (matched? (gensym "matched?"))
	     symb-hash
	     (end-symb (gensym "end")))

	(mapcar #'(lambda (node) 
		    (push (list node (gensym "node")) symb-hash)) dfa-states)
	(let ((node-code 
	       (mapcan 
		#'(lambda (node)
		    (let* ((node-symb (second (assoc node symb-hash)))
			   (final-state? (node-is-final? node))
			   (transitions (node-transitions node))
			   transitions-by-next-node)
		      (map nil (lambda (trans)
				 (let ((goto
					(second (assoc
						 (transition-next-node trans)
						 symb-hash))))
				   (if (not (assoc goto transitions-by-next-node))
				       (push (list 
					      goto 
					      (list 
					       (transition-value trans)))
					     transitions-by-next-node)
				       (push (transition-value trans)
					     (second 
					      (assoc goto transitions-by-next-node))))))
			   transitions)

		      (let ((trans-code 
			     (mapcar 
			      (lambda (x)
				(let* ((goto (first x))
				       (transition-values 
					(sort-codes-by-frequency
					 (find-code-ranges
					  (mapcar
					   (lambda (x)
					     (if (characterp x)
						 (char-code x)
						 x))
					   (second x)))))
				       (conditionals 
					(mapcar 
					 (lambda (val)
					   (cond ((listp val)
						  `(<= ,(first val)
						       ,char-code
						       ,(second val)))
						 ((numberp val)
						  `(= ,char-code ,val))
						 ((symbolp val)
						  `(,(gethash val transition-test-hash)
						     ,char-code))))
					 transition-values)))
				  `((or ,@conditionals)
				    ,(if goto 
					 (list 'go goto) 
					 (list 'go end-symb)))
				  ))
			      transitions-by-next-node)))
				    
	     
			`(,node-symb
			  ,@(if final-state?
				(list `(progn (setf ,matched? t)
					      (setf ,farthest-match ,i)))
				nil)
			  (if (= ,i ,strlen)
			      (go ,end-symb))
			  (setf ,char-code
				,(if *byte-mode*
				     `(aref ,string ,i)
				     `(char-code (aref ,string ,i))))
			  (incf ,i)
			  (cond 
			    ,@trans-code
			    ,(list 't (list 'go end-symb))))

			))) dfa-states)))

	  `(function (lambda (,string &optional (,i 0) (,strlen (length ,string)))
	     (declare 
	      (optimize (speed 3) (safety 0) (space 0) (debug 0))
	      (type fixnum ,i ,strlen)
	      (type (simple-array regex-char (*)) ,string))
	     (let* (,matched? 
		    (,farthest-match ,i)
		    (,char (aref ,string ,i))
		    (,char-code ,(if *byte-mode* 
				     char
				     `(char-code ,char))))
	       (declare (type regex-char ,char)
			(type regex-char-code ,char-code) 
			(type (or t nil) ,matched?))

	       (tagbody 
		  ,@node-code
		  ,end-symb)
	       (values ,matched? (- ,farthest-match 1)))))
	  )))))

;;;helper function, chains all of the functions that we have created thus far to generate
;;;list structure for the main 'compiled-regex' macro.
(defparameter *toggle* t)

(defun %compiled-regex (regex)
  (if *toggle* 
      (compile-greedy-dfa 
       (reduce-automaton (make-dfa (nfa-to-dfa-table (regexp-to-nfa regex)))))
      (compile-greedy-dfa2
       (reduce-automaton (make-dfa (nfa-to-dfa-table (regexp-to-nfa regex)))))))

;;;actual macro... will expand the lambda form in-line from a constant string.
   (defmacro compiled-regex (regex)
     (assert (stringp regex))
     (%compiled-regex regex))

;;;but what happens if we do not want to do a regex from a string? what if I want to generate my regex
;;;in line, or through a command line on the fly. You need a macro for that.
;;;pretty much, we take a form of some sort, which could evaluate to a string, and compile our regex
;;;on the fly.
   (defmacro regex (string)
     (if (stringp string)
	 (%compiled-regex string)
	 (let ((tmp-str (gensym "tmp-str")))
	   `(let ((,tmp-str ,string))
	      (let ((*standard-output* nil))
		(compile nil (eval (fast-regex::%compiled-regex ,tmp-str)))))))))

(declaim (optimize (speed 3) (space 0) (safety 0) (debug 0)))
;;;I hate to admit this, but I don't particularly care about the speed of the compiler...
;;;I find it more important to make sure that it is correct.

;;;one-pass scanner, takes a start and end. 
;;;note that we match from the 'start', which moves if we don't find a match,
;;; to the end... which is (generally) the length of the string.
;;;we return when we find a match. 
(defun scan (regex string &optional (start 0) (end (length string)))
  (declare (type fixnum start end)
	   (type (simple-array regex-char (*)) string))

  (loop for match-start of-type fixnum from start below end
     do (multiple-value-bind (ret match-end) (funcall 
					      (the (function ((simple-array regex-char (*)) fixnum fixnum))  regex)
					      string match-start end)
	  (when ret (return-from scan (values t match-start match-end)))))
  (values nil start end))


(defun first-longest-match (regex seq &optional (start 0) (end (length seq)))
  (loop for i from start below end do
       (loop for j from end above i do
	    ;(format t "~a~%" (subseq seq i j))
	    (when (funcall regex seq i j)
	      (return-from first-longest-match (values i j)))))
  nil)

(defun matches (regex seq &optional (start 0) (end (length seq)) accum)
  (multiple-value-bind (match-start match-end) (first-longest-match regex seq start end)
    (if (and match-start match-end)
	(longest-matches regex seq match-end end (cons (list match-start match-end) accum))
	accum)))

(defun do-matches ((match-start match-end (regex seq)) &body body)
  (let ((start (gensym "start"))
	(end (gensym "end"))
	(gseq (gensym "seq"))
	(gregex (gensym "regex")))
    `(let ((,start 0)
	   (,end (length seq))
	   (,gseq seq)
	   (,gregex regex))

       (do ()
	   (NIL)
	 (multiple-value-bind (,match-start ,match-end (first-longest-match ,gregex ,gseq ,start ,end))
	     (unless (and ,match-start ,match-end) (return))
	   ,@body)))))

(declaim (inline scan))

;;;macro that iterates through successive matches,
;;;(designed to assume greedy matches, non-overlaping)... will need to look into lazy matches.
;;;binding match start, and match end.
;;;it then evaluates 'body' when it finds a match.
;;;ends when we cannot find any other matches.
#|(defmacro do-scan ((match-start match-end regex string &optional (scan-start 0) scan-end) &body body)
  (assert (symbolp match-start))
  (assert (symbolp match-end))
  (let ((t-string (gensym "string"))
	(start (gensym "start"))
	(end (gensym "end"))
	(value (gensym "value")))

    `(let* ((,t-string ,string)
	    (,start ,scan-start)
	    (,end ,(or scan-end `(length ,t-string))))
       (declare (type (simple-array regex-char (*)) ,t-string)
		(type fixnum ,start ,end))
       (do ()
	   (NIL)
	 (multiple-value-bind (,value ,match-start ,match-end) (scan ,regex ,t-string ,start ,end)
	   (declare (type (or t null) ,value)
		    (type fixnum ,match-start ,match-end))
	   (if ,value
	       (progn ,@body (setf ,start ,match-end))
	       (return)))))))

(defmacro do-scan ((match-start match-end regex string &optional (scan-start 0) scan-end) &body body)
  (assert (symbolp match-start))
  (assert (symbolp match-end))
  (loop for i from scan-start to scan-end do
       (loop for j from i to scan-end do
	    (multiple-value-bind (value start end) (funcall regex string i j)


|#
;;;extract the start and end of all matches withing a string, as when
;;;matching by do-scan.
#|(defun matches (regex string &key (start 0) (end (length string)))
  (declare (type (simple-array regex-char (*)) string))

  (let (ret)
    (do-scan (i j regex string start end)
      (push (list i j) ret))
    (nreverse ret)))|#

;;;extract all matches, using 'matches', and then construct a similar string,
;;;which replaces those matches with the given replacement string.
;;;there is probably a way to do this more efficiently with regard to memory.
(defun regex-replace-all (regex string replacement &key (start 0) (end (length string)))
  (declare (type (simple-array regex-char (*)) string replacement))

  (let (matches
	(removed 0)
	(added 0)
	(replacement-length (length replacement))) 
    (declare (type fixnum removed added replacement-length))

    (do-scan (i j regex string start end)
      (incf removed (the fixnum (- j i)))
      (incf added replacement-length)
      (push i matches)
      (push j matches))

    (setf matches (nreverse matches))
    (let* ((new-array 
	    (make-array 
	     (+ (the fixnum (- end start)) (the fixnum (- added removed)))
	     :element-type 'regex-char))
	   (new-idx 0)
	   (old-idx start))
      (declare (type fixnum new-idx old-idx))

      (do* ((i (first matches) (first rmatches))
	    (j (second matches) (second rmatches))
	    (rmatches (cddr matches) (cddr rmatches)))
	   ((not j))

	(replace new-array string :start1 new-idx :start2 old-idx :end2 i)
	(incf new-idx (- i old-idx))
	(replace new-array replacement :start1 new-idx :start2 0)
	(incf new-idx replacement-length)
	(setf old-idx j))

      (replace new-array string :start1 new-idx :start2 old-idx :end2 end)
      new-array)))

;;;helper function for converting from a string to an array of character codes
;;;it is useful if you want to use regex-replace in byte-mode, as you will need
;;;to replace the bytes, with other bytes, rather than strings.
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun cb (string)
    (assert (stringp string))
    (if *byte-mode*
	(map '(simple-array (unsigned-byte 8) (*)) #'char-code string)
	string)))

(defmacro define-constant (name value &optional doc)
  `(defconstant ,name (if (boundp ',name) (symbol-value ',name) ,value)
     ,@(when doc (list doc))))

(defmacro make-regex-counter (regex)
  (assert (stringp regex))
  (let ((string (gensym))
	(start (gensym))
	(end (gensym))
	(s (gensym))
	(e (gensym))
	(count (gensym)))
    `(lambda (,string &optional (,start 0) (,end (length ,string)))
       (declare (type (simple-array regex-char  (*)) ,string)
		(type fixnum ,start ,end))
       (let ((,count 0))
	 (declare (type fixnum ,count))
	 (do-scan (,s ,e (regex ,regex) ,string ,start ,end)
	   (the fixnum (incf (the fixnum ,count))))
	 ,count))))

(defun clean-all (string)
  (regex-replace-all (regex "(>(\\w| )*\\n)|\\n") string #.(make-array 0 :element-type 'regex-char)))

(defmacro do-regex-counters (seq &rest strings)
  (assert (symbolp seq))
  `(progn ,@(mapcar #'(lambda (str)
			`(progn
			   (format t ,str)
			   (format t " ~s~%"
				   (funcall (make-regex-counter ,str)
					    ,seq)))) strings)))

(defmacro make-regex-replacer (regex replacement)
  (assert (stringp regex))
  (let ((seq (gensym)))
    `(lambda (,seq) (regex-replace-all (regex ,regex) ,seq ,replacement))))


(defmacro do-regex-replacers (seq &rest pairs)
  (assert (symbolp seq))
  `(progn ,@(mapcar 
	     #'(lambda (pair)
		 `(setf ,seq (funcall (make-regex-replacer ,@pair) ,seq))) pairs)))

(defun split-string (regex seq &aux (accum nil))
  (let ((begin 0))
    (do-scan (i j regex seq)
      (format t "~s~%" (list i j))
      (push (subseq seq begin i) accum)
      (setf begin j))
    (if (< begin (length seq))
	(push (subseq seq begin (length seq)) accum)))
  (nreverse accum))

;;;;;;;;;;REGEX-DNA-TEST
;;;;;;;;;;;;;;;;;;;;;;;;
#|
(defparameter *input-file* #p"/home/jon/Dropbox/regex/fasta-out.txt")

(defun main ()
  (with-open-file (stdin *input-file* :direction :input :element-type 'regex-char)
    (let ((string (make-array (the fixnum (file-length stdin)) :element-type 'regex-char)))
      (declare (type (simple-array regex-char (*)) string))
      (read-sequence string stdin)
      (format t "~s~%" (length string))
      (setf string (clean-all string))
      (format t "~s~%" (length string))
      (do-regex-counters string 
	"agggtaaa|tttaccct"
	"[cgt]gggtaaa|tttaccc[acg]"
	"a[act]ggtaaa|tttacc[agt]t"
	"ag[act]gtaaa|tttac[agt]ct"
	"agg[act]taaa|ttta[agt]cct"
	"aggg[acg]aaa|ttt[cgt]ccct"
	"agggt[cgt]aa|tt[acg]accct"
	"agggta[cgt]a|t[acg]taccct"
	"agggtaa[cgt]|[acg]ttaccct")
      (do-regex-replacers string
	("B" #.(cb "(c|g|t)"))
	("D" #.(cb "(a|g|t)"))
	("H" #.(cb "(a|c|t)")) 
	("K" #.(cb "(g|t)"))
	("M"  #.(cb "(a|c)"))
	("N"  #.(cb "(a|c|g|t)"))
	("R"  #.(cb "(a|g)"))   
	("S"  #.(cb "(c|t)"))
	("V"  #.(cb "(a|c|g)"))
	("W"  #.(cb "(a|t)"))
	("Y"   #.(cb "(c|t)")))
      (format t "~s~%" (length string)))))|#
