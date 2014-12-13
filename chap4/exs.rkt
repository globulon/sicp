;;;Ex 4-1
;;; define right to left evaluation
(define (list-of-values-left->right exps env)
  (if (no-operands? exps)
      '()
      (let ((evaluated (eval-exp (first-operand exps) env)))
        (cons evaluated (list-of-values-left->right exps env)))))

(define (list-of-values->rigth->left exps env)
  (if (no-operands? exps)
      '()
      (let ((remaining (list-of-values->rigth->left exps env)))
        (let ((evaluated (first-operand exps)))
          (cons evaluated remaining)))))