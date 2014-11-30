#lang racket/base
(require racket/match
         racket/list
         racket/flonum
         racket/fixnum
         racket/math)

(define (flclamp m x M)
  (flmax m (flmin x M)))

(define (flmodulo x y)
  (if (fl< x y)
      x
      (flmodulo (fl- x y) y)))

(define ((linear m M) t)
  (fl+ (fl* (fl- 1.0 t) m)
       (fl* t M)))
(define ((const v) t)
  v)
(define ((step m M) t)
  (if (fl< t 1.0)
      m
      M))

(struct *tl (len val stepf) #:transparent)
(define (tl len val stepf)
  (if (fl<= len 0.0)
      val
      (*tl len val stepf)))

(define (tl-len x)
  (if (*tl? x)
      (*tl-len x)
      0.0))
(define (tl-val x)
  (if (*tl? x)
      (*tl-val x)
      x))
(define (tl-step x step)
  (if (*tl? x)
      ((*tl-stepf x) step)
      x))

(define (tl-unit@ f tp)
  (define t (flclamp 0.0 tp 1.0))
  (tl (fl- 1.0 t)
      (f t)
      (λ (step)
        (tl-unit@ f (fl+ t step)))))

(define (tl-unit f)
  (tl-unit@ f 0.0))

(define (tl-superimpose comb left right)
  (tl (flmax (tl-len left)
             (tl-len right))
      (comb (tl-val left)
            (tl-val right))
      (λ (step)
        (tl-superimpose comb
                        (tl-step left step)
                        (tl-step right step)))))

(define (tl-loop/ inner current)
  (tl +inf.0
      (tl-val current)
      (λ (step)
        (if (fl< step (tl-len current))
            (tl-loop/ inner (tl-step current step))
            (tl-loop/ inner (tl-step inner (fl- step (tl-len current))))))))

(define (tl-loop inner)
  (tl-loop/ inner inner))

(define (tl-append left right)
  (if (fl<= (tl-len left) 0.0)
      right
      (tl (fl+ (tl-len left)
               (tl-len right))
          (tl-val left)
          (λ (step)
            (if (fl< step (tl-len left))
                (tl-append (tl-step left step) right)
                (tl-step right (fl- step (tl-len left))))))))

(define (tl-scale inner scale)
  (tl (fl* (tl-len inner) scale)
      (tl-val inner)
      (λ (step)
        (tl-scale (tl-step inner (fl/ step scale)) scale))))
(define (tl-map inner fun)
  (tl (tl-len inner)
      (fun (tl-val inner))
      (λ (step)
        (tl-map (tl-step inner step) fun))))

(define (tl-delay val delay inner)
  (tl-append (tl-scale (tl-unit (const val)) delay) inner))

(define (tl-superimpose* comb tls)
  (foldl (λ (right left) (tl-superimpose comb left right))
         (first tls) (rest tls)))
(define (tl-bind a b)
  (tl-superimpose (λ (av bv) (bv av)) a b))

;; xxx entity-component-system?

;; xxx something i dislike about these is that they require a
;; computation outside analyze the values. but maybe that IS the
;; "system" concept

(struct *tls *tl (id->tl) #:transparent)
(define (tls/ id->tl)
  (define-values (len val stepf)
    (for/fold ([len 0.0]
               [val (hasheq)]
               [stepf (λ (ht step) ht)])
              ([(id tl) (in-hash id->tl)])
      (values (fl+ len (tl-len tl))
              (hash-set val id (tl-val tl))
              (λ (ht step)
                (stepf (hash-set ht id (tl-step tl step)) step)))))

  (if (fl<= len 0.0)
      val
      (*tls len val
            (λ (step)
              (tls/ (stepf (hasheq) step)))
            id->tl)))
(define (tls)
  (hasheq))

;; xxx make this work on paths
(define (tls-id->tl x)
  (if (*tls? x) (*tls-id->tl x) x))
(define (tls-modify x f)
  (tls/ (f (tls-id->tl x))))
(define (tls-update x id f
                    [def (λ () (error 'tls-update "There is no mapping for ~v in ~e."
                                      id x))])
  (tls-modify x (λ (ht) (hash-update ht id f def))))
(define (tls-set x id v)
  (tls-modify x (λ (ht) (hash-set ht id v))))
(define (tls-remove x id)
  (tls-modify x (λ (ht) (hash-remove ht id))))
(define (tls-superimpose id->comb left right)
  (tls/
   (for/fold ([id->tl (tls-id->tl left)])
             ([(id tl) (in-hash (tls-id->tl right))])
     (if (hash-has-key? id->tl id)
         (hash-update id->tl id
                      (λ (old-tl)
                        (define comb (hash-ref id->comb id))
                        (tl-superimpose comb old-tl tl)))
         (hash-set id->tl id tl)))))

(module+ test
  (require lux
           lux/chaos/gui
           lux/chaos/gui/key
           lux/chaos/gui/val
           pict)

  (define W 1024)
  (define H 768)

  (define left-to-right
    (tl-unit (linear (* -0.125 W) (* +0.125 W))))
  (define right-to-left
    (tl-unit (linear (* +0.125 W) (* -0.125 W))))
  (define spinning
    (tl-unit (linear 0.0 (fl* 2.0 pi))))

  (define BCX (* 1/2 W))
  (define BCY (* 1/2 H))
  (define BR (sqrt (+ (sqr (/ BCX 3)) (sqr (/ BCY 3)))))
  (define (spinning-balls delta-big-theta)
    ;; xxx do i want these as separate functions or things inside of
    ;; "timeline"
    (tl-map
     (tls/
      (hasheq
       'radius
       (tl-loop
        (tl-scale (tl-append (tl-unit (linear 10.0 100.0))
                             (tl-unit (linear 100.0 10.0)))
                  120.0))
       'color
       (tl-loop
        (tl-scale (tl-append (tl-unit (const "black")) (tl-unit (const "red")))
                  30.0))
       'dx
       (tl-loop
        (tl-scale
         (tl-append left-to-right right-to-left)
         120.0))
       'theta
       (tl-loop (tl-scale spinning 360.0))))
     (λ (ht)
       (define radius (hash-ref ht 'radius))
       (define c (hash-ref ht 'color))
       (define d (hash-ref ht 'dx))
       (define theta (hash-ref ht 'theta))
       (λ (big-theta)
         (define C (make-polar BR (+ big-theta delta-big-theta)))
         (define CX (+ BCX (real-part C)))
         (define CY (+ BCY (imag-part C)))
         (define center-p
           (colorize (disk 5) "blue"))
         (define border-p
           (colorize (disk 30) c))
         (cons (vector (+ CX d) CY center-p)
               (for/list ([i (in-range 4)])
                 (define ith-theta (+ theta (/ (* i pi) 2)))
                 (define p (make-polar radius ith-theta))
                 (vector (+ (+ CX d) (real-part p))
                         (+ CY (imag-part p))
                         border-p)))))))

  (define combined
    (tl-bind
     (tl-loop (tl-scale spinning 360.0))
     (tl-superimpose*
      ;; xxx this is awkward
      (λ (x-fls y-fls)
        (λ (a)
          (append (x-fls a) (y-fls a))))
      (for/list ([i (in-range 4)])
        (define i.0 (fx->fl i))
        (tl-delay (λ (a) empty)
                  (fl* i.0 30.0)
                  (spinning-balls (fl/ (fl* i.0 pi) 2.0)))))))

  (define (pin-over* base l)
    (for/fold ([base base]) ([x*y*p (in-list l)])
      (match-define (vector x y p) x*y*p)
      (pin-over base x y p)))
  (define (pin-over*/lines base origin l)
    (define combined (pin-over* base l))
    (for/fold ([combined combined]) ([x*y*p (in-list l)])
      (match-define (vector _ _ p) x*y*p)
      (pin-line combined origin cc-find p cc-find)))

  (define init-tl 
    (tls-set (tls) 'main (tl-scale combined 0.5)))

  (struct example (gv tl)
          #:methods gen:word
          [(define (word-fps w)
             30.0)
           (define (word-event w e)
             (cond
              [(eq? e 'close)
               #f]
              [(key-event? e)
               (match (key-event-code e)
                 [#\space
                  (struct-copy
                   example w
                   [tl init-tl])]
                 [#\z
                  (struct-copy
                   example w
                   [tl (tls-superimpose (hasheq 'addtl append
                                                'main append)
                                        (example-tl w)
                                        init-tl)])]
                 [#\r
                  (struct-copy
                   example w
                   [tl (tls-remove (example-tl w) 'addtl)])]
                 [#\a
                  (struct-copy
                   example w
                   [tl
                    (tls-update
                     (example-tl w)
                     'addtl
                     (λ (old-tl)
                       (tl-map
                        (tl-scale (tl-unit (linear 5.0 100.0))
                                  60.0)
                        (λ (d)
                          (list (vector BCX BCY
                                        (colorize (disk d)
                                                  "green"))))))
                     #f)])]
                 [k
                  (printf "Ignoring ~v\n" k)
                  w])]
              [else
               w]))
           (define (word-tick w)
             (struct-copy
              example w
              [tl (tl-step (example-tl w) 1.0)]))
           (define (word-output w)
             (define ht (tl-val (example-tl w)))
             (define main-ps (hash-ref ht 'main '()))
             (define addtl-ps (hash-ref ht 'addtl '()))
             ((example-gv w) (pin-over* (pin-over* (blank W H) main-ps) addtl-ps)))])

  (call-with-chaos
   (make-gui)
   (λ ()
     (fiat-lux (example (make-gui/val) init-tl)))))
