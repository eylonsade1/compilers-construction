(define map
  (let ((null? null?)
	(car car) (cdr cdr)
	(cons cons) (apply apply))
  (letrec ((map-many
	    (lambda (f lists)
	      (if (null? (car lists))
		  '()
		  (cons
		   (apply f (map-one car lists))
		   (map-many f (map-one cdr lists))))))
	   (map-one
	    (lambda (f s)
	      (if (null? s)
		  '()
		  (cons (f (car s))
			(map-one f (cdr s)))))))
    (lambda (f . args)
      (map-many f args)))))


(define fold-left
  (lambda (fun init lst)
    (if (eq? lst '())
        init
        (fold-left fun (fun init (car lst)) (cdr lst)))))

(define fold-right
  (lambda (fun init lst)
    (if (eq? lst '())
        init
        (fun (car lst) (fold-right fun init (cdr lst))))))

(define cons*
 (lambda lst
   (fold-right cons '() lst)))
   
(define append
  (let ((null? null?)
	(fold-right fold-right)
	(cons cons))
    (lambda args
      (fold-right
       (lambda (e a)
	 (if (null? a)
	     e
	     (fold-right cons a e)))
       '() args))))

(define list (lambda x x))

(define list? 
  (let ((null? null?)
	(pair? pair?)
	(cdr cdr))
    (letrec ((list?-loop
	      (lambda (x)
		(or (null? x)
		    (and (pair? x)
			 (list?-loop (cdr x)))))))
      list?-loop)))

(define not
  (lambda (x) (if x #f #t)))


(define make-string
  (let ((null? null?) (car car)
	(make-string make-string))
    (lambda (x . y)
      (if (null? y)
	  (make-string x #\nul)
	  (make-string x (car y))))))



(let ((flonum? flonum?) (rational? rational?)
      (exact->inexact exact->inexact)
      (fold-left fold-left) (map map)
      (_+ +) (_* *) (_/ /) (_= =) (_< <)
      (car car) (cdr cdr) (null? null?))
  (let ((^numeric-op-dispatcher
	 (lambda (op)
	   (lambda (x y)
	     (cond
	      ((and (flonum? x) (rational? y)) (op x (exact->inexact y)))
	      ((and (rational? x) (flonum? y)) (op (exact->inexact x) y))
	      (else (op x y)))))))
      (set! + (lambda x (fold-left (^numeric-op-dispatcher _+) 0 x)))
      (set! * (lambda x (fold-left (^numeric-op-dispatcher _*) 1 x)))
      (set! / (let ((/ (^numeric-op-dispatcher _/)))
		(lambda (x . y)
		  (if (null? y)
		      (/ 1 x)
		      (fold-left / x y)))))
    (let ((^comparator
	   (lambda (op)
	     (letrec ((comparator
		       (lambda (x ys)
			 (or (null? ys)
			     (and (op x (car ys))
				  (comparator (car ys) (cdr ys)))))))
	       (lambda (x . y)
		 (comparator x y))))))
      (set! = (^comparator (^numeric-op-dispatcher _=)))
      (set! < (^comparator (^numeric-op-dispatcher _<))))))




