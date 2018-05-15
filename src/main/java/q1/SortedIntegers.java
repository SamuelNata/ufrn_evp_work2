package q1;

import java.util.Arrays;

public class SortedIntegers {
    /*@ public invariant (\forall int i;
    @                           0 < i && i < size;
    @                           arr[i-1] <= arr[i]);
    @*/
	
	
	private int arr[];
	private int capacity, size = 0;
	
	/*	@ public normal_behavior
		@ requires capacity>0;
		@ ensures arr.lenght==capacity;
		@ ensures size==0;
		@ */
	public SortedIntegers(int capacity) {
		this.capacity = capacity;
		this.arr = new int[capacity];
	}
	
	/*	@ public normal_behavior
		@ requires size<capacity;
		@ ensures this.contains(elem);
		@ ensures size == \old(size)+1;
		@ ensures (\forall int i; i!=elem; contains(i) <==> \old(contains(i)));
		@
		@ also
		@
		@ public normal_behavior
		@ requires size==capacity;
		@ ensures size == \old(size);
		@ ensures (\forall int i; i!=elem; contains(i) <==> \old(contains(i)));
		@ */
	public void add(int elem) {
		if(size<capacity) {
			int t = elem;
			int swap, idx=0;
			while(idx<size) {
				if(arr[idx]>elem) {
					size++;
					idx++;
					break;
				}
				idx++;
			}
			while(idx<size) {
				swap = arr[idx]; 
				arr[idx] = t;
				t = swap;
				idx++;
			}
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
	 	@ requires contains(elem);
		@ ensures size == \old(size)-1
		@ ensures (\forall int i; i!=elem; contains(i) <==> \old(contains(i)));
		@ */
	public void remove(int elem) {
		int idx=0;
		while(idx<size) {
			if(arr[idx]==elem) {
				break;
			}
			idx++;
		}
		if(idx<size) {
			while(idx<size-1) {
				arr[idx] = arr[idx+1];
				idx++;
			}
			size--;
		}
	}
	
	/*	@ public normal_behavior
		@ ensures size == \old(size)
		@ ensures \result == (\exists int i; i>=0 && i<=size; arr[i]==elem);
	*/
	public boolean contains(int elem) {
		for(int idx=0 ; idx<size ; idx++) {
			if(arr[idx]==elem) {
				return true;
			}
		}
		return false;
	}
	
	/*	Não sei o que esse metodo deve fazer.
	 */
	public int max() {
		return 0;
	}
	
	/*	@ public normal_behavior
		@ ensures size == \old(size)
		@ ensures (\forall int i; ; contains(i) <==> \old(contains(i)));
		@ ensures \result == size
	*/
	public int getSize() {
		return size;
	}
	
	/*	@ public normal_behavior
		@ ensures size == \old(size)
		@ ensures (\forall int i; ; contains(i) <==> \old(contains(i)));
		@ ensures \result == capacity
	*/
	public int getCapacity() {
		return capacity;
	}
	
	public String toString() {
		return Arrays.toString(arr);
	}
}
