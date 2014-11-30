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

(struct tl (len val stepf))
(define (tl-step tl step)
  ((tl-stepf tl) step))

(define-syntax-rule (rec name val)
  (letrec ([name val]) name))

(define (tl-unit@ f tp)
  (define t (flclamp 0.0 tp 1.0))
  (rec this
       (tl (fl- 1.0 t)
           (f t)
           (if (fl= 1.0 t)
               (λ (step)
                 this)
               (λ (step)
                 (tl-unit@ f (fl+ t step)))))))

(define (tl-unit f)
  (tl-unit@ f 0.0))

(define (tl-superimpose comb left right)
  (tl (max (tl-len left)
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
  (if (fl= 0.0 (tl-len inner))
      inner
      (tl (fl* (tl-len inner) scale)
          (tl-val inner)
          (λ (step)
            (tl-scale (tl-step inner (fl/ step scale)) scale)))))

(define (tl-delay val delay inner)
  (tl-append (tl-scale (tl-unit (const val)) delay) inner))

(define (tl-map inner fun)
  (tl (tl-len inner)
      (fun (tl-val inner))
      (λ (step)
        (tl-map (tl-step inner step) fun))))

(define (tl-superimpose* comb tls)
  (foldr (λ (left right) (tl-superimpose comb left right))
         (first tls) (rest tls)))
(define (tl-bind a b)
  (tl-superimpose (λ (av bv) (bv av)) a b))

;; xxx entity-component-system?

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
     (tl-superimpose
      cons
      (tl-superimpose
       cons
       (tl-loop
        (tl-append
         (tl-scale (tl-unit (linear 10.0 100.0))
                   60.0)
         (tl-scale (tl-unit (linear 100.0 10.0))
                   60.0)))
       (tl-loop
        (tl-scale (tl-append (tl-unit (step "black" "red"))
                             (tl-unit (step "red" "black")))
                  30.0)))
      (tl-superimpose
       cons
       (tl-loop
        (tl-append
         (tl-scale left-to-right 60.0)
         (tl-scale right-to-left 60.0)))
       (tl-loop (tl-scale spinning 360.0))))
     (match-lambda
      [(cons (cons radius c) (cons d theta))
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
                         border-p))))])))

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

  (struct example (gv tl)
          #:methods gen:word
          [(define (word-event w e)
             (cond
              [(eq? e 'close)
               #f]
              [(key-event? e)
               (match (let ()
                        (local-require racket/class)
                        (send e get-key-code))
                 [#\space
                  (struct-copy
                   example w
                   [tl combined])]
                 [#\a
                  (struct-copy
                   example w
                   [tl
                    (tl-superimpose
                     append
                     (example-tl w)
                     (tl-map
                      (tl-scale (tl-unit (linear 5.0 100.0))
                                60.0)
                      (λ (d)
                        (list (vector BCX BCY
                                      (colorize (disk d)
                                                "green"))))))])]
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
             (match-define ps (tl-val (example-tl w)))
             ((example-gv w) (pin-over* (blank W H) ps)))])

  (call-with-chaos
   (make-gui)
   (λ ()
     (fiat-lux (example (make-gui/val) combined)))))
