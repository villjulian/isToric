load ("isToric.sage")
R.<e,t,r,y,q,u,w,o> = PolynomialRing(QQ)
I = ideal (e*t-r*y-q*u+w*o, w*t-q*y-r*u+e*o, w*e-q*r-y*u+t*o)
ideal_is_toric(I)
