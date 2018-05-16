package q1;

import java.util.Arrays;

public class SortedIntegers {
    /*@ public invariant (\forall int i;
    @                           0 < i && i < size;
    @                           arr[i-1] <= arr[i]);
    @*/
	
	private /*@ spec_public @*/ int arr[];
	private /*@ spec_public @*/ int capacity, size = 0;
	
	public SortedIntegers(int capacity) {
		this.capacity = capacity;
		this.arr = new int[capacity];
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
			if(arr[begin+end/2]==elem) {
				target = begin+end/2;
				break;
			} else if(arr[begin+end/2]>elem) {
				end = (begin+end/2)-1;
			} else {
				begin = (begin+end/2)+1;
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
			if(arr[begin+end/2]==elem) {
				target = begin+end/2;
				break;
			} else if(arr[begin+end/2]>elem) {
				end = (begin+end/2)-1;
			} else {
				begin = (begin+end/2)+1;
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
			} else if(arr[begin+end/2]>elem) {
				end = (begin+end/2)-1;
			} else {
				begin = (begin+end/2)+1;
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
