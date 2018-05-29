package q1;

import java.util.Arrays;

public class SortedIntegers {
    /*	@ public invariant (\forall int i; 0 < i && i < size; arr[i-1] <= arr[i]);
	    @ */
	
	private /*@ spec_public @*/ int arr[] = null;
	private /*@ spec_public @*/ int capacity;
	private /*@ spec_public @*/ int size = 0;
	
	/*	@ public normal_behavior
	  	@ requires capacity>0;
	 	@ ensures this.capacity==capacity;
	 	@ ensures arr!=null;
	 	@ ensures arr.length()==this.capacity;
	 	@ */
	public SortedIntegers(int capacity) {
		this.capacity = capacity;
		this.arr = new int[this.capacity];
	}
	
	/*	@ public normal_behavior
		@ requires size<capacity;
		@ ensures size == \old(size)+1;
		@ ensures (\forall int i; i!=elem; contains(i) <==> \old(contains(i)));
		@ ensures \old(!contains(elem)) => contains(elem);
		@
		@ also
		@
		@ public normal_behavior
		@ requires size==capacity;
		@ ensures size == \old(size);
		@ ensures (\forall int i; ; contains(i) <==> \old(contains(i)));
		@ */
	public void add(int elem) {
		if(size==capacity) {	return;	}
		int begin=0, end=size, target=-1, idx;
		while(begin!=end) {
			if(arr[(begin+end)/2]==elem) {
				target = (begin+end)/2;
				break;
			} else if(arr[(begin+end)/2]>elem) {
				end = (begin+end)/2-1;
			} else {
				begin = (begin+end)/2+1;
			}
		}
		target = (arr[begin]<elem)? begin+1 : begin;
		if(target>=0) {
			idx=size++;
			while(idx>=target){
				arr[idx] = arr[--idx];
			}
			arr[target] = elem;
		}
	}
	
	/*	@ public normal_behavior
	 	@ requires contains(elem);
		@ ensures size == \old(size)-1
		@ ensures (\forall int i; i!=elem; contains(i) <==> \old(contains(i)));
		@ 
		@ also
		@
		@ public normal_behavior
	 	@ requires !contains(elem);
		@ ensures size == \old(size)
		@ ensures (\forall int i; i!=elem; contains(i) <==> \old(contains(i)));
		@ */
	public void remove(int elem) {
		int begin=0, end=size, target=-1;
		while(begin!=end) {
			if(arr[(begin+end)/2]==elem) {
				target = (begin+end)/2;
				break;
			} else if(arr[(begin+end)/2]>elem) {
				end = (begin+end)/2-1;
			} else {
				begin = (begin+end)/2+1;
			}
		}
		if(arr[begin]==elem){
			target = begin;
		}
		if(target>=0) {
			while(target<size-1) {
				arr[target] = arr[++target];
			}
			size--;
		}
	}
	
	/*	@ public normal_behavior
		@ ensures size == \old(size)
		@ ensures \result == (\exists int i; i>=0 && i<=size; arr[i]==elem);
	*/
	public /*@ pure @*/ boolean contains(int elem) {
		int begin=0, end=size;
		while(begin!=end) {
			if(arr[begin+end/2]==elem) {
				return true;
			} else if(arr[(begin+end)/2]>elem) {
				end = (begin+end)/2-1;
			} else {
				begin = (begin+end)/2+1;
			}
		}
		return arr[begin]==elem;
	}
	
	/*	@ public normal_behavior
		@ requires size>0;
		@ ensures 	(\exists int idx; idx>=0 && idx<size; arr[idx]==\result && 
		@ 					!(\forall int idy; idy>=0 && idy<size; !(arr[idy]>arr[idx]))
		@ 			);
	 */
	public /*@ pure @*/ int max() {
		return arr[size-1];
	}
	
	/*	@ public normal_behavior
		@ ensures \result == size
	*/
	public /*@ pure @*/ int getSize() {
		return size;
	}
	
	/*	@ public normal_behavior
		@ ensures \result == capacity
	*/
	public /*@ pure @*/ int getCapacity() {
		return capacity;
	}
	
	public String toString() {
		return Arrays.toString(arr);
	}
	
	/*	@ public normal_behavior
		@ ensures \result == 1; 
	 */
	public int a() {
		return 2;
	}
}


/*
1) b) Explique no relat�rio por que � �til usar invariantes; Ao explic�-lo, d� um exemplo concreto usando a especifica��o do m�todo de adicionar ou remover.

R: 	As invariantes no JML s�o uteis para evitar a reescrita de pr� e p�s condi��es em todos os metodos da classe, 
	j� que devem ser sempre atendidas antes e depois da execu��o dos metodos.
	Na classe SortedIntegers, que representa um container, o metodo contains verifica se um inteiro pertence ao container,
	para realizar essa tarefa de forma mais rapida podemos utilizar busca binaria, porem precisamos que o array esteja ordenado
	ent�o criamos este invariante, para verificar e garantir que os metodos que alteram o container ir�o mante-lo ordenado.
	A exemplo do metodo add, que adiciona um inteiro ao container, a busca binaria nos ajuda a encontrar o local onde o inteiro
	deve ser inserido no container para mante-lo ordenado, portanto a ordena��o do array deve ser uma pr� condi��o, e para que essa caracteristica possa
	ser utilizada novamente no futuro, � necesspario que seja mantida ap�s a execu��o do metodo, logo deve ser uma p�s condi��o.
	Abaixo est� a especifica��o das pr� e p�s condi��es do metodo add com o invariante replicado em cada metodo e com invariante na classe:
	
		//Com invariate replicado em casa metodo:
			@ public normal_behavior
			@ requires size<capacity;
			@ requires (\forall int i; 0 < i && i < size; arr[i-1] <= arr[i]);
			@ ensures size == \old(size)+1;
			@ ensures (\forall int i; i!=elem; contains(i) <==> \old(contains(i)));
			@ ensures \old(!contains(elem)) => contains(elem);
			@ ensures (\forall int i; 0 < i && i < size; arr[i-1] <= arr[i]);
			@ also
			@
			@ public normal_behavior
			@ requires size==capacity;
			@ requires (\forall int i; 0 < i && i < size; arr[i-1] <= arr[i]);
			@ ensures size == \old(size);
			@ ensures (\forall int i; ; contains(i) <==> \old(contains(i)));
			@ ensures (\forall int i; 0 < i && i < size; arr[i-1] <= arr[i]);
			
			
		//Com invariante na classe:
			@ public normal_behavior
			@ requires size<capacity;
			@ ensures size == \old(size)+1;
			@ ensures (\forall int i; i!=elem; contains(i) <==> \old(contains(i)));
			@ ensures \old(!contains(elem)) => contains(elem);
			@
			@ also
			@
			@ public normal_behavior
			@ requires size==capacity;
			@ ensures size == \old(size);
			@ ensures (\forall int i; ; contains(i) <==> \old(contains(i)));
			@
*/





