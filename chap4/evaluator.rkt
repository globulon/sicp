;;;#lang r5rs

(define (error reason . args)
  (display "Error: ")
  (display reason)
  (for-each (lambda (arg) 
              (display " ")
              (write arg))
            args)
  (newline)
  (scheme-report-environment 5)) 

(define (self-evaluating? exp)
  (cond ((number? exp) #t)
        ((string? exp) #t)
        (else false)))

(define (variable? exp)
  (symbol? exp))

(define (tagged-list? exp tag)
  (if (pair? exp)
      (eq? (car exp) tag)
      #f))

(define (quoted? exp)
  (tagged-list? exp 'quote))

(define (extract-quotation-text exp)
  (cdr exp))

(define (assignement? exp)
  (tagged-list? exp 'set!))

(define (extract-assignement-variable exp)
  (cadr exp))

(define (extract-assignement-value exp)
  (caddr exp))

(define (definition? exp)
  (tagged-list? exp 'define))

(define (extract-variable-name exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))

(define (extract-variable-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cdadr exp)
                   (caddr exp))))

(define (lambda? exp)
  (tagged-list? exp 'lambda))

(define (extract-lambda-params exp)
  (cadr exp))

(define (extract-lambda-body exp)
  (caddr exp))

(define (self-evaluating? exp)
  (cond ((number? exp) #t)
        ((string? exp) #t)
        (else #f)))

(define (application? exp)
  (pair? exp))

(define (operator exp)
  (car exp))

(define (operands exp)
  (cdr exp))

(define (no-operands? exps)
  (null? exps))

(define (first-operand exps)
  (car exps))

(define (rest-operands exps)
  (cdr exps))

(define (list-of-values exps env)
  (if (no-operands? exps)
      '()
      (cons (eval-exp (first-operand exps) env)
            (list-of-values (rest-operands exps) env))))

(define (if? exp)
  (tagged-list? exp 'if))

(define (extract-predicate exp)
  (cadr exp))

(define (extract-if-consequent exp)
  (caddr exp))

(define (extract-if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cdddr exp)
      ('false)))

(define (make-if predicate consequent alternate)
  (list 'if predicate consequent alternate))

(define (eval-if exp env)
  (if (true? (eval-exp (extract-predicate exp) env))
      (eval-exp (extract-if-consequent exp) env)
      (eval-exp (extract-if-alternative exp) env)))

(define (begin? exp)
  (tagged-list? exp 'begin))

(define (get-begin-actions exp)
  (cdr exp))

(define (last-exp? exps)
  (null? (cdr exps)))

(define (first-exp exps)
  (car exps))

(define (rest-exps exps)
  (cdr exps))

(define (sequence->exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))

(define (make-begin seq)
  (cons 'begin seq))

(define (cond? exp)
  (tagged-list? 'cond exp))

;;;(cond ((p) do) ((p2) do2) )
(define (cond-clauses exp) (cdr exp))

;;;((p) (do stuff))
(define (cond-predicate clause) 
  (car clause))

;;;((p) (do stuff))
(define (cond-actions clause)
  (cdr clause))

(define (cond-else-clause? clause)
  (equal? (con-predicate clause) 'else))

(define (cond->if exp)
  (expand-clauses (cond-clauses exp)))

(define (expand-clauses clauses)
  (cond ((null? clauses) 'false)
        ((cond-else-clause? (car clauses))
         (if (null? (rest clauses))
             (sequence->exp (cond-actions (car clauses)))
             (error "*ELSE* clause must be last clause")))
        (else 
         (let ((clause (car clauses)))
           (make-if (cond-predicate clause)
                    (sequence-exp (cond-actions clause))
                    (expand-clauses (rest clauses)))))))

(define (true? exp)
  (not (eq? exp #f)))

(define (false? exp)
  (not (eq? exp #f)))

(define (eval-sequence exps env)
  (cond ((last-exp? exps) (eval-exp (first-exp exps) env))
        (else (eval-exp (first-exp exps) env)
              (eval-sequence (rest-exps exps) env))))

(define (eval-assignement exp env)
  (set-variable-value! 
   (extract-assignement-variable exp)
   (extract-assignement-value exp)set-variable-value!
   env)
  'ok)

(define (eval-definition exp env)
  (define-variable! 
    (extract-variable-name exp)
    (extract-variable-value exp)
    env)
  'ok)

(define (make-procedure args body env)
  (list 'procedure args body env))

(define (compound-procedure? exp)
  (tagged-list? exp 'procedure))

(define (procedure-parameters p)
  (cadr p))

(define (procedure-body p)
  (caddr p))

(define (procedure-environment p)
  (cadddr p))

(define (enclosing-environment env) (cdr env))

(define (first-frame env) (car env))

(define empty-environment '())

;;; ((vars) val1 val2 ...)
(define (make-frame vars values)
  (cons vars values))

(define (frame-variables frame)
  (car frame))

(define (frame-values frame) 
  (cdr frame))

(define (add-binding-to-frame! var val frame)
  (set-car! frame (cons var (frame-variables frame)))
  (set-cdr! frame (cons val (frame-values frame))))

(define (extend-environment vars vals env)
  (cond ((eq? (length vars) (length vals))
         (cons (make-frame vars vals) env))
        ((< (length vars) (length vals))
         (error "*EXTEND ENV* not enough arguments applied"))
        (else 
         (error "*EXTEND ENV* too few arguments applied"))))

(define (lookup-variable v base-env)
  (define (look-up vars vals)
    (cond ((null? vars) '())
          ((eq? (car vars) v) (list (car vals)))
          (else (look-up (cdr vars) (cdr vals)))))
  (define (loop-env env)
    (if (eq? env empty-environment) 
        (error "Unbound variable" v)
        (let ((first (first-frame env)))
          (let ((result (look-up (frame-variables first) 
                                 (frame-values first))))
            (if (null? result)
                (loop-env (enclosing-environment env))
                (car result))))))
  (loop-env base-env))


(define (set-variable-value! var val base-env)
  (define (set-frame-variable! vars vals)
    (cond ((null? vars) '())
          ((eq? (car vars) var) 
           (begin 
             (set-car! vals val)
             (list var)))
          (else (set-frame-variable! (cdr vars) (cdr vals)))))
  (define (set-env-variable! env)
    (if (eq? env empty-environment) 
        (error "Cannot bind into empty environment" var)       
        (let ((frame (first-frame env)))
          (let ((result (set-frame-variable! (frame-variables frame) (frame-values frame))))
            (if (null? result)
                (set-env-variable! (enclosing-environment env))
                (car result))))))
  (set-env-variable! base-env))

(define (define-variable! var val env)
  (let ((frame (first-frame env)))
    (define (add-var! vars vals)
      (cond ((null? vars) 
             (add-binding-to-frame! var val frame))
            ((eq? var (car vars)) 
             (set-car! vals val))
            (else (add-var! (cdr vars) (cdr vals)))))
    (add-var! (frame-variables frame) (frame-values frame))))

(define (primitive? exp)
  (tagged-list? exp 'primitive))

(define (primitive-implementation proc)
  (cadr proc))

(define (apply-primitive-proc proc args)
  (apply (primitive-implementation proc) args))

(define (apply-proc procedure arguments)
  (cond ((primitive? procedure) 
         (apply-primitive-proc procedure arguments))
        ((compound-procedure? procedure)
         (eval-sequence 
          (extract-body procedure)
          (extend-environment
           (extract-parameters procedure)
           arguments
           (extract-environment procedure))))))

(define (eval-exp exp env)
  (cond ((self-evaluating? exp) exp)
        ((variable? exp) (lookup-variable exp env))
        ((quoted? exp) (extract-quotation-text exp))
        ((assignement? exp) (eval-assignement exp env))
        ((definition? exp) (eval-definition exp env))
        ((if? exp) (eval-if exp env))
        ((lambda? exp)
         (make-procedure (extract-lambda-parameters exp)
                         (extract-lambda-body exp)
                         env))
        ((begin? exp)
         (eval-sequence (get-begin-actions exp) env))
        ((cond? exp) (eval-exp (cond->if exp) env))
        ((application? exp) 
         (apply-proc (eval-exp (operator exp) env)
                     (list-of-values (operands exp) env)))
        (else (error "Unknown expression -- EVAL" exp))))

(define primitive-procedures
  (list (list 'car car)
        (list 'cdr cdr)
        (list 'cons cons)
        (list 'append append)
        (list '+ +)
        (list '* *)))

(define (primitive-procedure-names)
  (map car primitive-procedures))

(define (primitive-procedure-objects)
  (map (lambda (proc) (list 'primitive (cadr proc)))
       primitive-procedures))

(define (setup-environment)
  (let ((initial-env
         (extend-environment (primitive-procedure-names)
                             (primitive-procedure-objects)
                             empty-environment)))
    (define-variable! 'true #t initial-env)
    (define-variable! 'false #f initial-env)
    initial-env))


(define global-environment (setup-environment))

(define input-prompt ";;;M-Eval input:")
(define output-prompt ";;;M-Eval value:")

(define (prompt-for-input prompt)
  (newline) 
  (newline) 
  (newline) 
  (display prompt) 
  (newline))

(define (anounce-output prompt)
  (newline) 
  (display prompt) 
  (newline))

(define (user-print output)
  (if (compound-procedure? output)
      (display (list 'compound-procedure
                     (procedure-parameters output)
                     (procedure-body output)
                     '<procedure-env>))
      (display output)))

(define (driver-loop)
  (prompt-for-input input-prompt)
  (let ((input (read)))
    (let ((output (eval-exp input global-environment)))
      (anounce-output output-prompt)
      (user-print output)))
  (driver-loop))
