package q2;

public class Question2 {
	int a, b, c;
	
	/*@ normal_behaviour
	@ requires a <= b;
	@ ensures a <= b;
	@*/
	public Question2 (int _a, int _b, int _c){
		this.a = _a; this.b = _b; this.c = _c;
	}
	
	/*@ normal_behaviour
	@ requires a <= b;
	@ ensures a <= b && b <= c &&
	@(a == \old(a) && b == \old(b) && c == \old(c) ||
	@ a == \old(a) && b == \old(c) && c == \old(b) ||
	@ a == \old(b) && b == \old(a) && c == \old(c) ||
	@ a == \old(b) && b == \old(c) && c == \old(a) ||
	@ a == \old(c) && b == \old(a) && c == \old(b) ||
	@ a == \old(c) && b == \old(b) && c == \old(a));
	@ */
	public void isorttriple ( ){
		if(a>b) {	return;	}
		int temp=0;
		if(a<=c) {
			if(b<=c) {
				return;
			} else {
				temp = c;
				c = b;
				b = temp;
			}
		} else { 
			temp = a;
			a = c;
			c = temp;
			if(b<=c) {
				return;
			} else {
				temp = c;
				c = b;
				b = temp;
			}
		}
	}
}




/*
 * 2) b)
pre = {a<=b && a==a0 && b==b0 && c==c0}
pos = 	{	a <= b && b <= c &&
			(a == a0 && b == b0 && c == c0 ||
			 a == a0 && b == c0 && c == b0 ||
			 a == b0 && b == a0 && c == c0 ||
			 a == b0 && b == c0 && c == a0 ||
			 a == c0 && b == a0 && c == b0 ||
			 a == c0 && b == b0 && c == a0)		}
			 
			 
Init demonstration:
{a<=b && a==a0 && b==b0 && c==c0}
[]
{
	if(a>b) {	return;	}
	int temp=0;
	if(a<=c) {
		if(b<=c) {
			return;
		} else {
			temp = c;
			c = b;
			b = temp;
		}
	} else { 
		temp = a;
		a = c;
		c = temp;
		if(b<=c) {
			return;
		} else {
			temp = c;
			c = b;
			b = temp;
		}
	}
}
pos
----------------------------------------------------------- Conditional rule 1.1
{a<=b && a==a0 && b==b0 && c==c0 && a>b}
[]
{
	return;
}
pos
----------------------------------------------------------- Exit
a<=b && a==a0 && b==b0 && c==c0 && a>b ==>	pos 
--------------------------------------------------- a<=b && a>b is false, and false && _ is false
false ==>	pos
[ true from (a<=b && a>b)==false and x -> y same as ¬x V y ]
----------------------------------------------------------- Conditional rule 1.2 + update rule
{a<=b && a==a0 && b==b0 && c==c0}
[temp:=0]
{
	if(a<=c) {
		if(b<=c) {
			return;
		} else {
			temp = c;
			c = b;
			b = temp;
		}
	} else { 
		temp = a;
		a = c;
		c = temp;
		if(b<=c) {
			return;
		} else {
			temp = c;
			c = b;
			b = temp;
		}
	}
}
pos
----------------------------------------------------------- Conditional rule 1.2.1
{a<=b && a==a0 && b==b0 && c==c0 && a<=c}
[temp:=0]
{
	if(b<=c) {
		return;
	} else {
		temp = c;
		c = b;
		b = temp;
	}
}
pos
----------------------------------------------------------- Conditional rule 1.2.1.1
{a<=b && a==a0 && b==b0 && c==c0 && a<=c && b<=c}
[temp:=0]
{ return; }
pos
----------------------------------------------------------- Exit 
a<=b && a==a0 && b==b0 && c==c0 && a<=c && b<=c ==> [temp:=0] (	a <= b && b <= c &&
										(a == a0 && b == b0 && c == c0 ||
										 a == a0 && b == c0 && c == b0 ||
										 a == b0 && b == a0 && c == c0 ||
										 a == b0 && b == c0 && c == a0 ||
										 a == c0 && b == a0 && c == b0 ||
										 a == c0 && b == b0 && c == a0)		)
------------------------------------------ apply temp defintion and assume a<=b && a==a0 && b==b0 && c==c0 && a<=c && b<=c
(	true && true &&
	(true && true && true ||
	 true && b == c0 && c == b0 ||
	 a == b0 && b == a0 && true ||
	 a == b0 && b == c0 && c == a0 ||
	 a == c0 && b == a0 && c == b0 ||
	 a == c0 && true && c == a0)		)
------------------------------------------ simplifying 
(	true &&	(true || b == c0 && c == b0 ||
			 a == b0 && b == a0 ||
			 a == b0 && b == c0 && c == a0 ||
			 a == c0 && b == a0 && c == b0 ||
			 a == c0 && c == a0)	)
------------------------------------------ simplifying 
(	true &&	(true ) )
[true && true is true]
----------------------------------------------------------- Conditional rule 1.2.1.2
{a<=b && a==a0 && b==b0 && c==c0 && a<=c && b>c}
[]
{
	temp = c;
	c = b;
	b = temp;
}
pos
----------------------------------------------------------- Parallel update
{a<=b && a==a0 && b==b0 && c==c0 && a<=c && b>c}
[temp:=c | c:=b | b:=c]
{}
pos
----------------------------------------------------------- Exit
(a<=b && a==a0 && b==b0 && c==c0 && a<=c && b>c) ==>
 				[temp:=c | c:=b | b:=c]
 				(	a <= b && b <= c &&
				(a == a0 && b == b0 && c == c0 ||
				 a == a0 && b == c0 && c == b0 ||
				 a == b0 && b == a0 && c == c0 ||
				 a == b0 && b == c0 && c == a0 ||
				 a == c0 && b == a0 && c == b0 ||
				 a == c0 && b == b0 && c == a0)		)
------------------------------------------ apply def
(a<=b && a==a0 && b==b0 && c==c0 && a<=c && b>c) ==>
 			(	a <= b && b <= c &&
				(a == a0 && c == b0 && b == c0 ||
				 a == a0 && c == c0 && b == b0 ||
				 a == b0 && c == a0 && b == c0 ||
				 a == b0 && c == c0 && b == a0 ||
				 a == c0 && c == a0 && b == b0 ||
				 a == c0 && c == b0 && b == a0)		)
------------------------------------------ Assume a<=b && a==a0 && b==b0 && c==c0 && a<=c && b>c
 			(	true && c <= b &&
				(true && c == b0 && b == c0 ||
				 true && true && true ||
				 a == b0 && c == a0 && b == c0 ||
				 a == b0 && true && b == a0 ||
				 a == c0 && c == a0 && true ||
				 a == c0 && c == b0 && b == a0)		)
------------------------------------------ c<=b from b>c and simplifying
 			(	true &&
				( c == b0 && b == c0 ||
				 true ||
				 a == b0 && c == a0 && b == c0 ||
				 a == b0 && b == a0 ||
				 a == c0 && c == a0 ||
				 a == c0 && c == b0 && b == a0)		)
[true from true && (true || _ )]
----------------------------------------------------------- Conditional rule 1.2.2
{a<=b && a==a0 && b==b0 && c==c0}
[temp:=0]
{ 
	temp = a;
	a = c;
	c = temp;
	if(b<=c) {
		return;
	} else {
		temp = c;
		c = b;
		b = temp;
	}
}
pos
----------------------------------------------------------- Parallel updates
{a<=b && a==a0 && b==b0 && c==c0}
[temp:=a | a:=c | c:=a]
{
	if(b<=c) {
		return;
	} else {
		temp = c;
		c = b;
		b = temp;
	}
}
pos
----------------------------------------------------------- Conditional rule 1.2.2.1 
{a<=b && a==a0 && b==b0 && c==c0 && b<=c}
[temp:=a | a:=c | c:=a]
{ return; }
pos
----------------------------------------------------------- Exit
(a<=b && a==a0 && b==b0 && c==c0 && b<=c) ==> 
			[temp:=a | a:=c | c:=a]
			(a <= b && b <= c &&
				(a == a0 && b == b0 && c == c0 ||
				 a == a0 && b == c0 && c == b0 ||
				 a == b0 && b == a0 && c == c0 ||
				 a == b0 && b == c0 && c == a0 ||
				 a == c0 && b == a0 && c == b0 ||
				 a == c0 && b == b0 && c == a0)  )
----------------------------------------------------------- apply defs
(a<=b && a==a0 && b==b0 && c==c0 && b<=c) ==> 
			(c <= b && b <= a &&
				(c == a0 && b == b0 && a == c0 ||
				 c == a0 && b == c0 && a == b0 ||
				 c == b0 && b == a0 && a == c0 ||
				 c == b0 && b == c0 && a == a0 ||
				 c == c0 && b == a0 && a == b0 ||
				 c == c0 && b == b0 && a == a0)  )
----------------------------------------------------------- assume (a<=b && a==a0 && b==b0 && c==c0 && b<=c) and simplify
(a<=b && a==a0 && b==b0 && c==c0 && b<=c) ==> 
			(c <= b && b <= a &&
				(c == a0 && true && a == c0 ||
				 c == a0 && b == c0 && a == b0 ||
				 c == b0 && b == a0 && a == c0 ||
				 c == b0 && b == c0 && true ||
				 true && b == a0 && a == b0 ||
				 true && true && true)  )
----------------------------------------------------------- FIQUEI COM DUVIDA AQUI, DEPOIS EU CONTINUO 



POS = {	a <= b && b <= c &&
			(a == a0 && b == b0 && c == c0 ||
			 a == a0 && b == c0 && c == b0 ||
			 a == b0 && b == a0 && c == c0 ||
			 a == b0 && b == c0 && c == a0 ||
			 a == c0 && b == a0 && c == b0 ||
			 a == c0 && b == b0 && c == a0)		}

*/
