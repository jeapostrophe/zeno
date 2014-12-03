#lang racket/base
(require racket/match
         racket/set
         racket/flonum)

;; Entity : Number
;; xxx perhaps with a mask of what components are enabled
;; xxx if every component has a spot for every entity then we use lots
;; of memory
;; xxx if each entity has a spot to say which offset into the
;; component it uses, then they each need their own free list

;; Component : Entity -> Data
(struct *component (field->i) #:transparent)
(define (make-*component fields)
  (*component
   (for/hasheq ([f (in-list fields)]
                [i (in-naturals)])
     (values f i))))
(define-syntax-rule (component (id ...) format)
  (make-*component '(id ...)))
(define (com-init com)
  (make-vector (hash-count (*component-field->i com))))
(define (com-ref com vec k)
  (vector-ref vec (hash-ref (*component-field->i com) k)))
(define (com-set! com vec k v)
  (vector-set! vec (hash-ref (*component-field->i com) k) v))

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

(struct *rvector (vec) #:transparent #:mutable)
(define (rvector size)
  (*rvector (make-vector size #f)))
(define (rvector-size rv)
  (vector-length (*rvector-vec rv)))
(define (rvector-resize! rv new-size)
  (define new (make-vector new-size #f))
  (vector-copy! new 0 (*rvector-vec rv))
  (set-*rvector-vec! rv new))
(define (rvector-set! rv i v)
  (vector-set! (*rvector-vec rv) i v))
(define (rvector-ref rv i)
  (vector-ref (*rvector-vec rv) i))

(struct *gvector (hd keys rv) #:transparent #:mutable)
(define (gvector)
  (*gvector 0 (mutable-seteq) (rvector 1)))
(define (gvector-alloc! gv expanded!)
  (match gv
    [(*gvector #f keys vec)
     (define old-len (rvector-size vec))
     (define new-len (* 2 old-len))
     (rvector-resize! vec new-len)
     (for ([i (in-range old-len new-len)])
       (rvector-set! vec i (+ i 1)))
     (rvector-set! vec (- new-len 1) #f)
     (set-*gvector-hd! gv old-len)
     (expanded! new-len)
     (gvector-alloc! gv void)]
    [(*gvector hd keys vec)
     (set-add! keys hd)
     (set-*gvector-hd! gv (rvector-ref vec hd))
     hd]))
(define (gvector-free! gv i)
  (rvector-set! (*gvector-rv gv) i (*gvector-hd gv))
  (set-remove! (*gvector-keys gv) i)
  (set-*gvector-hd! gv i))
(define (gvector-set! gv i v)
  (rvector-set! (*gvector-rv gv) i v))
(define (gvector-ref gv i)
  (rvector-ref (*gvector-rv gv) i))
(define (gvector-update! gv i f)
  (gvector-set! gv i (f (gvector-ref gv i))))
(define (gvector-keys gv)
  (set->list (*gvector-keys gv)))

(struct *system (es com->id com->ht interests pob) #:transparent)
(define (system #:components coms
                #:processor-order po)
  (define pob (box #f))
  (define sys
    (*system (gvector)
             (for/hasheq ([c (in-list coms)]
                          [i (in-naturals)])
               (values c i))
             (for/vector ([c (in-list coms)]
                          [i (in-naturals)])
               (rvector 1))
             (make-hasheq)
             pob))

  (set-box! pob
            (for/list ([ps (in-list po)])
              (for/list ([p (in-list ps)])
                (define-values (com-set init) (p sys))
                (hash-set! (*system-interests sys) com-set #t)
                (cons com-set init))))

  sys)
(define (*system-com-id sys com)
  (hash-ref (*system-com->id sys) com
            (λ ()
              (error '*system-com-id "No ~v" com))))
(define (*system-com-ref sys com)
  (define comi (*system-com-id sys com))
  (vector-ref (*system-com->ht sys) comi))

(define (system-iterate sys)
  (for ([ps (in-list (unbox (*system-pob sys)))])
    ;; xxx can do each level of this tree in parallel
    (for ([cs*i (in-list ps)])
      (system-process sys cs*i))))
(define (system-process sys cs*i)
  (match-define (cons com-set init) cs*i)
  (define process-entity (init))
  (for ([e (in-entities sys)]
        #:when (entity-has? sys e com-set))
    (process-entity e)))

(define (entity-alloc! sys)
  (define es (*system-es sys))
  (define e
    (gvector-alloc! es
                    (λ (new-size)
                      (for ([ht (in-vector (*system-com->ht sys))])
                        (rvector-resize! ht new-size)))))
  (gvector-set! es e 0)
  e)
(define (entity-delete! sys e)
  (define es (*system-es sys))
  (gvector-free! es e))

(define (in-entities sys)
  ;; xxx it is necessary to get them all first because we might remove
  ;; entities in the middle of systems.
  (in-list (gvector-keys (*system-es sys))))
(define (entity-has! sys e com)
  (rvector-set! (*system-com-ref sys com) e (com-init com))
  (printf "Setting ~v for ~v\n" e com)
  (gvector-update! (*system-es sys) e
                   (λ (cms) (component-union (component-singleton sys com) cms))))
;; xxx entity-has-not!
(define (component-singleton sys x)
  (arithmetic-shift 1 (*system-com-id sys x)))
(define (component-union x y)
  (bitwise-ior x y))
(define (entity-mask sys e)
  (gvector-ref (*system-es sys) e))
(define (entity-has? sys e com-set)
  (define em (entity-mask sys e))
  (define m (bitwise-and com-set em))
  (= com-set m))
(define (*entity-set! sys e com field val)
  (com-set! com (rvector-ref (*system-com-ref sys com) e)
            field val))
(define-syntax-rule (entity-set! sys e com field val)
  (*entity-set! sys e com 'field val))
(define (*entity-ref sys e com field)
  (com-ref com (rvector-ref (*system-com-ref sys com) e)
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
;; inside here (which would allow fast access to its information
;; rather than the lookup inside)
(define Moving
  (λ (sys)
    (values
     (component-union (component-singleton sys Position)
                      (component-singleton sys Velocity))
     (λ ()
       (λ (e)
         (entity-set! sys e Position x
                      (fl+ (entity-ref sys e Position x)
                           (entity-ref sys e Velocity dx)))
         (entity-set! sys e Position y
                      (fl+ (entity-ref sys e Position y)
                           (entity-ref sys e Velocity dy))))))))

;; xxx make this predictive when there's a Pos & Velocity
(define Colliding
  (λ (sys)
    (values
     (component-union
      (component-singleton sys Position)
      (component-singleton sys Collideable))
     (λ ()
       (define rs null)
       (λ (l)
         (for ([r (in-list rs)])
           (when (and (= (entity-ref sys l Position x)
                         (entity-ref sys r Position x)))
             (entity-has! sys l Collided)
             (entity-set! sys l Collided other-data
                          (entity-ref sys r Collideable data))
             (entity-has! sys r Collided)
             (entity-set! sys r Collided other-data
                          (entity-ref sys l Collideable data))))
         (set! rs (cons l rs)))))))

(define Exploding
  (λ (sys)
    (values
     (component-union
      (component-singleton sys Position)
      (component-singleton sys Collided))
     (λ ()
       (λ (e)
         (define explosion (entity-alloc! sys))
         (entity-has! sys explosion Position)
         (entity-set! sys explosion Position x (entity-ref sys e Position x))
         (entity-set! sys explosion Position y (entity-ref sys e Position y))
         (entity-delete! sys e))))))

(define (print-system sys)
  (local-require racket/pretty)
  (pretty-print sys)
  (printf "\n"))

(module+ test
  (define Game
    (system
     #:components
     (list Position Velocity Collideable Collided)
     #:processor-order
     ;; xxx discover this from the dependency information
     ;; and meta-data about what processors modify
     (list (list Moving)
           (list Colliding)
           (list Exploding))))

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
    (system-iterate Game)
    (print-system Game)))
