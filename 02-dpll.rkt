#lang typed/racket/base
(require racket/set racket/list racket/match racket/string)

(define-type P (U Symbol (cons '¬ Symbol)))
(define-type Disj (Setof P))
(define-type Conj (Setof Disj))
(define-type Assignment (HashTable Symbol Boolean))
(define ∅ : (Setof Nothing) {set})

(define (format-P [x : P])
  (cond [(cons? x) (format "¬~a" (cdr x))]
        [else (symbol->string x)]))

(define (format-Disj [x : Disj])
  (string-join (for/list : (Listof String) ([P (in-set x)]) (format-P P))
               " ∨ "))

(define (format-Conj [x : Conj])
  (string-join (for/list : (Listof String) ([d (in-set x)]) (format "(~a)" (format-Disj d)))
               " ∧ "))

(define (format-Assignment [x : Assignment])
  (string-join (for/list : (Listof String) ([(p b) (in-hash x)]) (format "~a ↦ ~a" p b))
               ", "
               #:before-first "{"
               #:after-last "}"))

(: sat-solve : Conj → (U #f Assignment))
;; Straightforward DPLL SAT solver
(define (sat-solve φ)
  
  ;; Naive arbitrary pick
  (define (next-var [φ : Conj])
    (match (set-first (set-first φ))
      [(cons _ p) p]
      [(? symbol? p) p]))
  
  (let sat-solve/acc : (U #f Assignment) ([φ φ] [asn : Assignment (hash)])
    (cond
      [(set-empty? φ) asn]
      [(set-member? φ ∅) #f]
      [else
       (define p₁ (next-var φ))
       (or
        (sat-solve/acc
         (for/set: : Conj ([disjᵢ (in-set φ)] #:unless (set-member? disjᵢ p₁))
           (set-remove disjᵢ (cons '¬ p₁)))
         (hash-set asn p₁ #t))
        (sat-solve/acc
         (for/set: : Conj ([disjᵢ (in-set φ)] #:unless (set-member? disjᵢ (cons '¬ p₁)))
           (set-remove disjᵢ p₁))
         (hash-set asn p₁ #f)))])))

(define (test-out [φ : Conj])
  (define ans (sat-solve φ))
  (cond [ans (printf "~a sat by ~a~n" (format-Conj φ) (format-Assignment ans))]
        [else (printf "~a is unsat~n" (format-Conj φ))]))
