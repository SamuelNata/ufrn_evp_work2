package q3;

public class Question3 {
    
    /*@ public normal_behavior
     @ ensures \result == (\old(n)*\old(m));
     @ ensures n == 0;
     @*/
   int mul (int m, int n){
       int res = 0;
       if (n < 0) {
           n = -n;
           m = -m;
       } else {
       }
       
       //@ maintaining  0 <= n;
       //@ decreasing n; 
       while (n>0) {
           res = res + m;
           n = n - 1;
       }
       
       return res;
   }
   public static void main(String args[]) {
       Question3 q3 = new Question3();
       System.out.println("Result = " + q3.mul(4, 4));
   }
}

