method Main() {
	var qs: seq<seq<int>> :=
		[[ 1, 3,-2, 7, 0],
		 [-1,-2, 2,17,-5],
		 [ 2, 2, 1,-4,-3],
		 [ 0, 0, 1, 7,17],
		 [-2, 8,-2, 2, 8]];

	var min,max := ExtremeElements(qs);

	assert min == -5 && max == 17 by
	{
		assert qs[1][4] == -5;
		assert qs[3][4] == 17;
		assert forall i,j :: 0 <= i < 5 && 0 <= j < 5 ==> -5 <= qs[i][j] <= 17;
	}

	print "The smallest element in ";
	print qs;
	print " is ";
	print min;
	print " and the largest element is ";
	print max;
}


method ExtremeElements(qs: seq<seq<int>>) returns (min: int, max: int)
	requires qs != [] && qs[0] != []
	ensures exists row: nat :: row < |qs| && min in qs[row]
	ensures exists row: nat :: row < |qs| && max in qs[row]
	ensures forall row: nat, column: nat :: row < |qs| && column < |qs[row]| ==> min <= qs[row][column] <= max
{
	min, max := qs[0][0], qs[0][0];
	var i: nat,j: nat := 0,1;
	while i != |qs|
		invariant Inv1(qs,i,j,min,max)
		decreases |qs|-i
	{
		i,j,min,max := EE1(qs,i,j,min,max);
	}
}

method EE1(qs: seq<seq<int>>, i0: nat, j0: nat, min0: int, max0: int) returns (i: nat, j: nat, min: int, max: int)
	requires Inv1(qs,i0,j0,min0,max0)
	requires i0 != |qs|
	ensures Inv1(qs,i,j,min,max)
	ensures 0 <= |qs|-i < |qs|-i0
	{
		i,j,min,max:=i0,0,min0,max0;
		// from postcondition
		assert i0 != |qs|;
		// from Inv1
		assert i0 <= |qs|;
		assert i0 < |qs|; // by i0 != |qs| &&  i0 <= |qs| ==> i0 < |qs|
		assert i < |qs|; // by i:=i0
		assert i < |qs| ==> j <= |qs[i]|;
		assert min <= max;
		
		assert (forall row: nat,column: nat :: (row < i && column < |qs[row]|) || (row == i < |qs| && column < j) ==> min <= qs[row][column] <= max);
		
		assert i < |qs|;
		
		if(|qs[i]|>0){
			
			var k1:int :=max1(qs[i]);
			if(max<k1){
				max:= k1;
			}else{}

			var k2:int :=min1(qs[i]);
			if(min>k2){
				min:= k2;
			}else{}

		}else{}
		assert (exists row: nat,column: nat :: ((row < i && column < |qs[row]|) || (row == i < |qs| && column < |qs[i]|)) && min == qs[row][column]);
		assert (exists row: nat,column: nat :: ((row < i && column < |qs[row]|) || (row == i < |qs| && column < |qs[i]|)) && max == qs[row][column]);

		i:=i+1;
	
	}

predicate Inv1(qs: seq<seq<int>>, i: nat, j: nat, min: int, max: int)
{
	i <= |qs| &&
	(i < |qs| ==> j <= |qs[i]|) && min <= max &&
	(exists row: nat,column: nat :: ((row < i && column < |qs[row]|) || (row == i < |qs| && column < j)) && min == qs[row][column]) &&
	(exists row: nat,column: nat :: ((row < i && column < |qs[row]|) || (row == i < |qs| && column < j)) && max == qs[row][column]) &&
	(forall row: nat,column: nat :: (row < i && column < |qs[row]|) || (row == i < |qs| && column < j) ==> min <= qs[row][column] <= max)
}


method max1(a:seq<int>) returns(max:int)
 requires |a|>0;
 ensures (forall j :int :: (j >= 0 && j < |a| ==> max >= a[j]));
 ensures (|a| > 0)==>(exists j : int :: j>=0 && j < |a| && max==a[j]);
{
	 if (|a| == 0)  { max := 0;} 
 
	 else {
		 max:=a[0];
		 var i:int :=1;
		 while(i < |a|)
		 invariant (i<=|a|) && (forall j:int :: j>=0 && j<i ==> max >= a[j]) && (exists j:int :: j>=0 && j<i && max==a[j]);
		 decreases (|a|-i); 
		 {
			 if(a[i] > max){max := a[i];}
			 i := i + 1;
 
		 }
	 }
} 

method min1(a:seq<int>) returns(min:int)
 requires |a|>0;
 ensures (forall j :int :: (j >= 0 && j < |a| ==> min <= a[j]));
 ensures (|a| > 0)==>(exists j : int :: j>=0 && j < |a| && min==a[j]);
{
	 if (|a| == 0)  { min := 0;} 
 
	 else {
		 min:=a[0];
		 var i:int :=1;
		 while(i < |a|)
		 invariant (i<=|a|) && (forall j:int :: j>=0 && j<i ==> min <= a[j]) && (exists j:int :: j>=0 && j<i && min==a[j]);
		 decreases (|a|-i); 
		 {
			 if(a[i] < min){min := a[i];}
			 i := i + 1;
 
		 }
	 }
}


