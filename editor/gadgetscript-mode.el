;;; gadgetscript-mode.el --- major mode for gadgetscript  -*- lexical-binding: t -*-

;; font locking and comment syntax for the .gs files that gadget compiles.
;; there is no indentation engine, gadgetscript has no block structure worth one.

;;; Code:

(defvar gadgetscript-mode-syntax-table
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?\( "()1n" table)
    (modify-syntax-entry ?\) ")(4n" table)
    (modify-syntax-entry ?* ". 23n" table)
    (modify-syntax-entry ?_ "_" table)
    (modify-syntax-entry ?' "_" table)
    (dolist (c '(?+ ?- ?/ ?% ?< ?> ?= ?& ?| ?! ?. ?:))
      (modify-syntax-entry c "." table))
    table)
  "Syntax table for `gadgetscript-mode'.")

(defconst gadgetscript-keywords
  '("let" "rec" "in" "if" "then" "else" "fun"))

(defconst gadgetscript-builtins
  '("not" "fst" "snd" "float_of_int" "int_of_float"))

(defconst gadgetscript-font-lock-keywords
  `((,(concat "\\_<" (regexp-opt gadgetscript-keywords) "\\_>")
     . font-lock-keyword-face)
    (,(concat "\\_<" (regexp-opt gadgetscript-builtins) "\\_>")
     . font-lock-builtin-face)
    ("\\_<\\(true\\|false\\)\\_>" . font-lock-constant-face)
    ("\\_<\\(Int\\|Bool\\|Float\\|Unit\\)\\_>" . font-lock-type-face)
    ("\\_<let\\s-+rec\\s-+\\([a-z_][A-Za-z0-9_']*\\)" 1 font-lock-function-name-face)
    ("\\_<let\\s-+\\([a-z_][A-Za-z0-9_']*\\)\\s-*(" 1 font-lock-function-name-face)
    ("\\_<let\\s-+\\([a-z_][A-Za-z0-9_']*\\)\\s-*[=:]" 1 font-lock-variable-name-face)
    ("\\_<[0-9]+\\(\\.[0-9]*\\([eE][-+]?[0-9]+\\)?\\)?\\_>" . font-lock-constant-face)
    ("->" . font-lock-operator-face))
  "Font lock rules for `gadgetscript-mode'.")

;;;###autoload
(define-derived-mode gadgetscript-mode prog-mode "GadgetScript"
  "Major mode for editing gadgetscript source."
  :syntax-table gadgetscript-mode-syntax-table
  (setq-local comment-start "(* ")
  (setq-local comment-end " *)")
  (setq-local comment-start-skip "(\\*+[ \t]*")
  (setq-local font-lock-defaults '(gadgetscript-font-lock-keywords)))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.gs\\'" . gadgetscript-mode))

(provide 'gadgetscript-mode)
;;; gadgetscript-mode.el ends here
