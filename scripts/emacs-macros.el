(defun coq-get-constructors ()
  "Get the list of constructors in the current adt.  Assumes that we are positioned right before the first constructor.  Leaves point set to right before the final period in the definition"
  (if (char-equal (char-after) ?.)
      nil ; no data constructors
					; for the first case, the | is optional
    (when (char-equal (char-after) ?|)
      (forward-char)
      (forward-comment (buffer-size)))
    
    (cons (thing-at-point 'word)
	  (progn
	    (forward-word)
	    (forward-comment (buffer-size))
	    (while (not (or
			 (char-equal (char-after) ?.)
			 (char-equal (char-after) ?|)))
	      (forward-char)
	      (forward-comment (buffer-size)))
	    (coq-get-constructors)))))

(defun coq-find-start-inductive ()
  "returns the point at the start of the current Inductive declaration"
    (save-excursion
      (forward-comment (buffer-size))
      (if (string-equal (thing-at-point 'word) "Inductive")
					; we are right before or in the middle of Inductive
	  (car (bounds-of-thing-at-point 'word))
					; we are assumed to be somewhere in the middle of the string
	      (let ((case-fold-search nil)) ; ensure that the search is case-sensitive
		(search-backward "Inductive"))
	      )))

(defun coq-get-inductive-info ()
  "Returns a (start-point end-point name constrs...) list of the components of the current adt.  start is right before the I in Inductive, and end is right after the ."
  (save-excursion
    (let ((start (coq-find-start-inductive)))
      (goto-char start)
      (forward-word)
      (forward-comment (buffer-size))
      (let ((adt-name (thing-at-point 'sexp)))
	(search-forward ":=")
	(forward-comment (buffer-size))
	(let ((constructor-names (coq-get-constructors)))
	  (forward-char)
	  (cons start
		 (cons (point)
		       (cons adt-name
			     constructor-names))))))))
	  

(defun coq-make-cases-tactic ()
  "Defines a cases tactic based on the current inductive definition"
  (interactive)
  (save-excursion
    (let* ((case-var "c")
	   (inductive-info (coq-get-inductive-info))
	   (start (pop inductive-info))
	   (end (pop inductive-info))
	   (adt-name (pop inductive-info))
	   (constructor-names inductive-info))
      (goto-char end)
      (insert "\n"
	      "Tactic Notation \""
	      adt-name
	      "_cases\" tactic(first) ident(" case-var ") :=\n"
	      "  first;\n"
	      "  [ "
	      (mapconcat
	       (lambda (constr) (concat "Case_aux " case-var " \"" constr "\"%string"))
	       constructor-names
	       "\n  | ")
	      "]."
	      ))))
