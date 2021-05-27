l_n =: >. @: (% & 2) @: #
left =: monad define
	#.(l_n y) {. y
)

r_n =: <. @: (% & 2) @: #
right =: monad define
	#.(-(r_n y)) {. y
)

num_n =: #@#:

NB. x  (value to adjust), y (x;y, adjust if y > x)
adjust =: dyad define
	fst =: {. > y
	sec =: {: > y
	if. sec > fst
	   do. (((num_n sec) - num_n fst) $ 0),(#:x)
	else.
	   #:x
	end.
)

caramul =: dyad define
	n =. (num_n x) >. (num_n y)

	if. n = 1
		do. x * y
	else.
		yy =. y adjust y;x
		xx =. x adjust x;y

		lx =. left xx
		ly =. left yy
		rx =. right xx
		ry =. right yy

		P1 =. lx mult ly
		P2 =. rx mult ry
		P3 =. (lx + rx) mult ry + ly

		n_div2 =. <.n%2 
		P2 + (P1 * 2 ^ 2 * n_div2) + (P3 - P1 + P2) * 2 ^ n_div2
	end.
)
