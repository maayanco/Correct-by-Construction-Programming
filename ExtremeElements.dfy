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

		assert i0 != |qs|;
		// from Inv1
		assert i0 <= |qs|;
		assert i0 < |qs|; // by i0 != |qs| &&  i0 <= |qs| ==> i0 < |qs|
		assert i < |qs|; // by i:=i0
		assert i < |qs| ==> j <= |qs[i]|;
		assert min <= max;
		
		assert (forall row: nat,column: nat :: (row < i && column < |qs[row]|) || (row == i < |qs| && column < j) ==> min <= qs[row][column] <= max);
		
		assert i < |qs|;
		
		if(|qs[i]|>0)
		{
			
			var k1:int :=Max(qs[i]);
			var k2:int :=Min(qs[i]);
						
			if(max<k1) && (min>k2)
			{
				max,min:= k1,k2;
			}
			else if(max<k1)
			{
				max:=k1;
			}
			else if(min>k2)
			{
				min:=k2;
			}
			else
			{
			}

		}
		else
		{
		}

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


method Max(a:seq<int>) returns(max:int)
 requires |a|>0
 ensures (forall j :int :: (j >= 0 && j < |a| ==> max >= a[j]))
 ensures (|a| > 0)==>(exists j : int :: j>=0 && j < |a| && max==a[j])
{

	max:=a[0];
	var i:int :=1;
	while(i < |a|)
	invariant (i<=|a|) && (forall j:int :: j>=0 && j<i ==> max >= a[j]) && (exists j:int :: j>=0 && j<i && max==a[j])
	decreases (|a|-i) 
	{
		if(a[i] > max)
		{
			max := a[i];
		}
		i := i + 1;
	}
	 
} 


method Min(a:seq<int>) returns(min:int)
 requires |a|>0;
 ensures (forall j :int :: (j >= 0 && j < |a| ==> min <= a[j]));
 ensures (|a| > 0)==>(exists j : int :: j>=0 && j < |a| && min==a[j]);
{

	min:=a[0];
	var i:int :=1;
	while(i < |a|)
	invariant (i<=|a|) && (forall j:int :: j>=0 && j<i ==> min <= a[j]) && (exists j:int :: j>=0 && j<i && min==a[j]);
	decreases (|a|-i) 
	{
		if(a[i] < min)
		{
			min := a[i];
		}
		i := i + 1;
	}
	 
} 



/** Annotated Versions */

/**

	method EE1'(qs: seq<seq<int>>, i0: nat, j0: nat, min0: int, max0: int) returns (i: nat, j: nat, min: int, max: int)
	requires Inv1(qs,i0,j0,min0,max0)
	requires i0 != |qs|
	ensures Inv1(qs,i,j,min,max)
	ensures 0 <= |qs|-i < |qs|-i0
	{

		i,j,min,max:=i0,0,min0,max0; 
	
		assert i0 != |qs|;
		// from Inv1
		assert i0 <= |qs|;
		assert i0 < |qs|; // by i0 != |qs| &&  i0 <= |qs| ==> i0 < |qs|
		assert i < |qs|; // by i:=i0
		assert i < |qs| ==> j <= |qs[i]|;
		assert min <= max;
		
		assert (forall row: nat,column: nat :: (row < i && column < |qs[row]|) || (row == i < |qs| && column < j) ==> min <= qs[row][column] <= max);
		
		assert i < |qs|;
		
		if(|qs[i]|>0)
		{
			assert |qs[i]|>0; //if-guard
			
			var k1:int :=Max(qs[i]);
			var k2:int :=Min(qs[i]);
						
			if(max<k1) && (min>k2)
			{
				assert max<k1 && min>k2; //if-guard

				assert Inv1(qs,i+1,j,k2,k1);
				assert 0 <= |qs|-(i+1) < |qs|-i0;
				max,min:= k1,k2;
				assert Inv1(qs,i+1,j,min,max);
				assert 0 <= |qs|-(i+1) < |qs|-i0;
			}
			else if(max<k1)
			{
				assert max<k1; //if-guard

				assert Inv1(qs,i+1,j,min,k1);
				assert 0 <= |qs|-(i+1) < |qs|-i0;
				max:=k1;
				assert Inv1(qs,i+1,j,min,max);
				assert 0 <= |qs|-(i+1) < |qs|-i0;
			}
			else if(min>k2)
			{
				assert min>k2; //if-guard

				assert Inv1(qs,i+1,j,k2,max);
				assert 0 <= |qs|-(i+1) < |qs|-i0;
				min:=k2;
				assert Inv1(qs,i+1,j,min,max);
				assert 0 <= |qs|-(i+1) < |qs|-i0;
			}
			else
			{	
				assert !(max<k1) && !(min>k2); //not if-guards 

				assert Inv1(qs,i+1,j,min,max);
				assert 0 <= |qs|-(i+1) < |qs|-i0;
			}
			assert Inv1(qs,i+1,j,min,max);
			assert 0 <= |qs|-(i+1) < |qs|-i0;
		}
		else
		{
			assert |qs[i]|<=0; //!if-guard

			assert Inv1(qs,i+1,j,min,max);
			assert 0 <= |qs|-(i+1) < |qs|-i0;
		}

		assert (exists row: nat,column: nat :: ((row < i && column < |qs[row]|) || (row == i < |qs| && column < |qs[i]|)) && min == qs[row][column]);
		assert (exists row: nat,column: nat :: ((row < i && column < |qs[row]|) || (row == i < |qs| && column < |qs[i]|)) && max == qs[row][column]);

		assert Inv1(qs,i+1,j,min,max);
		assert 0 <= |qs|-(i+1) < |qs|-i0;

		i:=i+1;
		
		assert Inv1(qs,i,j,min,max);
		assert 0 <= |qs|-i < |qs|-i0;
	
	}


method Max'(a:seq<int>) returns(max:int)
 requires |a|>0;
 ensures (forall j :int :: (j >= 0 && j < |a| ==> max >= a[j]));
 ensures (|a| > 0)==>(exists j : int :: j>=0 && j < |a| && max==a[j]);
{
	
	assert |a|>0; //pre-condition
	
	max:=a[0];

	assert (1<=|a|) && (forall j:int :: j>=0 && j<1 ==> max >= a[j]) && (exists j:int :: j>=0 && j<1 && max==a[j]);

	var i:int :=1;

	assert (i<=|a|) && (forall j:int :: j>=0 && j<i ==> max >= a[j]) && (exists j:int :: j>=0 && j<i && max==a[j]);

	while(i < |a|)
	invariant (i<=|a|) && (forall j:int :: j>=0 && j<i ==> max >= a[j]) && (exists j:int :: j>=0 && j<i && max==a[j]);
	decreases (|a|-i) 
	{
		if(a[i] > max)
		{
			assert a[i]>max; //guard
			assert (i+1<=|a|) && (forall j:int :: j>=0 && j<i+1 ==> a[i] >= a[j]) && (exists j:int :: j>=0 && j<i+1 && a[i]==a[j]);
			max := a[i];
			assert (i+1<=|a|) && (forall j:int :: j>=0 && j<i+1 ==> max >= a[j]) && (exists j:int :: j>=0 && j<i+1 && max==a[j]);
		}
		else
		{
			assert a[i]<=max; //!if-guard
			assert (i+1<=|a|) && (forall j:int :: j>=0 && j<i+1 ==> max >= a[j]) && (exists j:int :: j>=0 && j<i+1 && max==a[j]);
		}
		assert (i+1<=|a|) && (forall j:int :: j>=0 && j<i+1 ==> max >= a[j]) && (exists j:int :: j>=0 && j<i+1 && max==a[j]);
		i := i + 1;
		assert (i<=|a|) && (forall j:int :: j>=0 && j<i ==> max >= a[j]) && (exists j:int :: j>=0 && j<i && max==a[j]);
	}
	assert i>=|a|; //!guard
	assert (i<=|a|) && (forall j:int :: j>=0 && j<i ==> max >= a[j]) && (exists j:int :: j>=0 && j<i && max==a[j]); //inv
	
	//==> 
	
	assert i==|a|;
	assert |a|>0; //pre-cond

	// ==>
	
	assert (forall j :int :: (j >= 0 && j < |a| ==> max >= a[j]));
	assert (|a| > 0)==>(exists j : int :: j>=0 && j < |a| && max==a[j]);
} 


method Min'(a:seq<int>) returns(min:int)
 requires |a|>0;
 ensures (forall j :int :: (j >= 0 && j < |a| ==> min <= a[j]));
 ensures (|a| > 0)==>(exists j : int :: j>=0 && j < |a| && min==a[j]);
{
	
	assert |a|>0; //pre-condition

	min:=a[0];
	
	assert (1<=|a|) && (forall j:int :: j>=0 && j<1 ==> min <= a[j]) && (exists j:int :: j>=0 && j<1 && min==a[j]);

	var i:int :=1;

	assert (i<=|a|) && (forall j:int :: j>=0 && j<i ==> min <= a[j]) && (exists j:int :: j>=0 && j<i && min==a[j]);

	while(i < |a|)
	invariant (i<=|a|) && (forall j:int :: j>=0 && j<i ==> min <= a[j]) && (exists j:int :: j>=0 && j<i && min==a[j]);
	decreases (|a|-i) 
	{
		if(a[i] < min)
		{
			assert a[i]<min; //guard
			assert (i+1<=|a|) && (forall j:int :: j>=0 && j<i+1 ==> a[i] <= a[j]) && (exists j:int :: j>=0 && j<i+1 && a[i]==a[j]);
			min := a[i];
			assert (i+1<=|a|) && (forall j:int :: j>=0 && j<i+1 ==> min <= a[j]) && (exists j:int :: j>=0 && j<i+1 && min==a[j]);
		}
		else
		{	
			assert a[i]>=min; //!if-guard
			assert (i+1<=|a|) && (forall j:int :: j>=0 && j<i+1 ==> min <= a[j]) && (exists j:int :: j>=0 && j<i+1 && min==a[j]);
		}
		assert (i+1<=|a|) && (forall j:int :: j>=0 && j<i+1 ==> min <= a[j]) && (exists j:int :: j>=0 && j<i+1 && min==a[j]);
		i := i + 1;
		assert (i<=|a|) && (forall j:int :: j>=0 && j<i ==> min <= a[j]) && (exists j:int :: j>=0 && j<i && min==a[j]);
	}
	assert i>=|a|; //!guard
	assert (i<=|a|) && (forall j:int :: j>=0 && j<i ==> min <= a[j]) && (exists j:int :: j>=0 && j<i && min==a[j]); //inv
	
	//==> 
	
	assert i==|a|;
	assert |a|>0; //pre-cond
	// ==>
	
	assert (forall j :int :: (j >= 0 && j < |a| ==> min <= a[j]));
	assert (|a| > 0)==>(exists j : int :: j>=0 && j < |a| && min==a[j]);
} 

*/