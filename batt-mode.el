;; batt-mode.el -- BATT major emacs mode

(defvar batt-font-lock-keywords
 '(
   ("--.*" . 'font-lock-comment-face)
   ("\\<\\(let\\|in\\)\\>\\|@\\|:\\|=" . font-lock-keyword-face)
   ("\\<\\(true\\|false\\|tt\\|refl\\)\\>" . font-lock-constant-face)
   ("\\<\\(U\\|Type\\|Bool\\|Unit\\|Empty\\)\\>\\|->\\|→\\|⨂\\|⊗\\|≡\\|⊥\\|♭\\|𝄫" . font-lock-builtin-face)
   ("\\<\\(\\)\\>" . font-lock-constant-face)
   ("^\\([^ (=]*\\)" 1 'font-lock-function-name-face)
  )
)

(defvar batt-mode-syntax-table
  (let ((st (make-syntax-table)))
    ;; Allow some extra characters in words
    (modify-syntax-entry ?_ "w" st)
    ;; Comments
    (modify-syntax-entry ?- ". 12" st)
    (modify-syntax-entry ?\n ">" st)
    st)
  "Syntax table for BATT major mode.")

(defvar batt-tab-width 4)

(define-derived-mode batt-mode fundamental-mode
  "BATT" "Major mode for BATT files."
  :syntax-table batt-mode-syntax-table
  (set (make-local-variable 'comment-start) "--")
  (set (make-local-variable 'comment-start-skip) "--+\\s-*")
  (set (make-local-variable 'font-lock-defaults) '(batt-font-lock-keywords))
  (setq mode-name "BATT")
)

(provide 'batt-mode)

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.batt\\'" . batt-mode))
