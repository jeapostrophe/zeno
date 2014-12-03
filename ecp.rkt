#lang racket/base
(require racket/match
         racket/flonum)

;; Entity : Number
;; xxx perhaps with a mask of what components are enabled
;; xxx if every component has a spot for every entity then we use lots
;; of memory
;; xxx if each entity has a spot to say which offset into the
;; component it uses, then they each need their own free list

;; Component : Entity -> Data
(struct *component (fields))
(define-syntax-rule (component (id ...) format)
  (*component '(id ...)))

;; xxx ideally these will be giant vectors, some being flvector, some
;; being fx, some being bytes or shared.

(define Position (component (x y) #:flonum))
(define Cell (component (x y) #:fixnum))
(define Tint (component (r g b) #:byte))
(define Collideable (component (shape data) #:racket))
(define Collided (component (other-data) #:racket))
(define Velocity (component (dx dy) #:flonum))
(define Display (component (disp) #:racket))
(define Render (component (x y disp) #:racket))

(struct *system ([next #:mutable] es com->id po))
(define (system #:components coms
                ;; xxx discover this from the dependency information
                ;; and meta-data about what processors modify
                #:processor-order po)
  (*system 0 (make-hasheq)
           (for/hasheq ([c (in-list coms)]
                        [i (in-naturals)])
             (values c i))
           po))
(define (*system-com-ref sys com)
  (hash-ref (*system-com->id sys) com))

(define (system-iterate sys)
  (for ([ps (in-list (*system-po sys))])
    ;; xxx can do each level of this tree in parallel
    (for ([p (in-list ps)])
      (p sys))))

(define (entity-alloc! sys)
  (define es (*system-es sys))
  (define e (*system-next sys))
  (hash-set! es e (make-hasheq))
  (set-*system-next! sys (+ 1 e))
  e)
(define (entity-delete! sys e)
  (define es (*system-es sys))
  (hash-remove! es e))

(define (in-entities sys)
  ;; xxx it is necessary to get them all first because we might remove
  ;; entities in the middle of systems.
  (in-list (hash-keys (*system-es sys))))
(define (entity-has! sys e com)
  (hash-set! (hash-ref (*system-es sys) e) (*system-com-ref sys com) (make-hasheq)))
(define (component-and x y)
  (cons x y))
(define (entity-has? sys e com)
  (match com
    [(cons x y)
     (and (entity-has? sys e x)
          (entity-has? sys e y))]
    [_
     (hash-has-key? (hash-ref (*system-es sys) e) 
                    (*system-com-ref sys com))]))
(define (*entity-set! sys e com field val)
  (hash-set! (hash-ref (hash-ref (*system-es sys) e) 
                       (*system-com-ref sys com))
             field val))
(define-syntax-rule (entity-set! sys e com field val)
  (*entity-set! sys e com 'field val))
(define (*entity-ref sys e com field)
  (hash-ref (hash-ref (hash-ref (*system-es sys) e) 
                      (*system-com-ref sys com))
            field))
(define-syntax-rule (entity-ref sys e com field)
  (*entity-ref sys e com 'field))

;; xxx I dislike that there could be many systems like this that are
;; performing identical logic "animating" different kinds of things.
;; so they must be values that are produced by functions and thus they
;; need to abstract over the components
;;
;; xxx processors should expose their query, what they (might) change,
;; and how often they need to be run (always, on changes, etc)
;;
;; xxx should be testable
;;
;; xxx the system should not use the component directly, but should
;; have its own notion of that particular component, which is bound
;; inside here
(define Moving
  (λ (sys)
    (for ([e (in-entities sys)]
          #:when (entity-has? sys e (component-and Position Velocity)))
      (entity-set! sys e Position x
                   (fl+ (entity-ref sys e Position x)
                        (entity-ref sys e Velocity dx)))
      (entity-set! sys e Position y
                   (fl+ (entity-ref sys e Position y)
                        (entity-ref sys e Velocity dy))))))

;; xxx make this predictive when there's a Pos & Velocity
;;
;; xxx maybe i shouldn't have these 'pair' queries and instead have
;; processors with state
(define Colliding
  (λ (sys)
    (for ([l (in-entities sys)]
          #:when (entity-has? sys l (component-and Position Collideable)))
      (for ([r (in-entities sys)]
            #:unless (eq? l r)
            #:when (entity-has? sys r (component-and Position Collideable)))
        (when (and (= (entity-ref sys l Position x)
                      (entity-ref sys r Position x)))
          (entity-has! sys l Collided)
          (entity-set! sys l Collided other-data
                       (entity-ref sys r Collideable data))
          (entity-has! sys r Collided)
          (entity-set! sys r Collided other-data
                       (entity-ref sys l Collideable data)))))))

(define Exploding
  (λ (sys)
    (for ([e (in-entities sys)]
          #:when (entity-has? sys e (component-and Position Collided)))
      (define explosion (entity-alloc! sys))
      (entity-has! sys explosion Position)
      (entity-set! sys explosion Position x (entity-ref sys e Position x))
      (entity-set! sys explosion Position y (entity-ref sys e Position y))
      (entity-delete! sys e))))

(define Printing
  (λ (sys)
    (local-require racket/pretty)
    (pretty-print (*system-es sys))
    (printf "\n")))

(module+ test
  (define Game
    (system
     #:components
     (list Position Velocity Collideable Collided)
     #:processor-order
     (list (list Moving)
           (list Colliding)
           (list Exploding)
           (list Printing))))

  (define Hero (entity-alloc! Game))
  (entity-has! Game Hero Position)
  (entity-set! Game Hero Position x 5.0)
  (entity-set! Game Hero Position y 5.0)
  (entity-has! Game Hero Velocity)
  (entity-set! Game Hero Velocity dx .50)
  (entity-set! Game Hero Velocity dy .50)
  (entity-has! Game Hero Collideable)
  (entity-set! Game Hero Collideable shape 'rect)
  (entity-set! Game Hero Collideable data 'Frog)

  (define Roof (entity-alloc! Game))
  (entity-has! Game Roof Position)
  (entity-set! Game Roof Position x 7.0)
  (entity-set! Game Roof Position y 0.0)
  (entity-has! Game Roof Collideable)
  (entity-set! Game Roof Collideable shape 'rect)
  (entity-set! Game Roof Collideable data 'Ceiling)

  (for ([i (in-range 5)])
    (system-iterate Game)))
