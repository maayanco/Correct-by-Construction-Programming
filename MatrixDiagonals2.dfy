method Main() {
	var m: array2<int> := new int[5,5];
	m[0,0],m[0,1],m[0,2],m[0,3],m[0,4] :=  1, 3,-2, 7, 0;
	m[1,0],m[1,1],m[1,2],m[1,3],m[1,4] := -1,-2, 2,17,-5;
	m[2,0],m[2,1],m[2,2],m[2,3],m[2,4] :=  2, 2, 1,-4,-3;
	m[3,0],m[3,1],m[3,2],m[3,3],m[3,4] :=  0, 0, 1, 7,17;
	m[4,0],m[4,1],m[4,2],m[4,3],m[4,4] := -2, 8,-2, 2, 8;

	var sum := MatrixDiagonal(m,5,2);
	print sum;
	assert sum == 12 by {
		calc {
			MatrixDiagSum(m,5,2);
		==
			SumOnD(m,5,2,0,0,0);
		==
			SumOnD(m,5,2,0,1,0);
		==
			SumOnD(m,5,2,0,2,0);
		==
			SumOnD(m,5,2,0,3,m[0,2]);
		==
			SumOnD(m,5,2,0,4,m[0,2]);
		==
			SumOnD(m,5,2,0,5,m[0,2]);
		==
			SumOnD(m,5,2,1,0,m[0,2]);
		==
			SumOnD(m,5,2,1,1,m[0,2]);
		==
			SumOnD(m,5,2,1,2,m[0,2]);
		==
			SumOnD(m,5,2,1,3,m[0,2]);
		==
			SumOnD(m,5,2,1,4,m[0,2]+m[1,3]);
		==
			SumOnD(m,5,2,1,5,m[0,2]+m[1,3]);
		==
			SumOnD(m,5,2,2,0,m[0,2]+m[1,3]);
		==
			SumOnD(m,5,2,2,1,m[0,2]+m[1,3]+m[2,0]);
		==
			SumOnD(m,5,2,2,2,m[0,2]+m[1,3]+m[2,0]);
		==
			SumOnD(m,5,2,2,3,m[0,2]+m[1,3]+m[2,0]);
		==
			SumOnD(m,5,2,2,4,m[0,2]+m[1,3]+m[2,0]);
		==
			SumOnD(m,5,2,2,5,m[0,2]+m[1,3]+m[2,0]+m[2,4]);
		==
			SumOnD(m,5,2,3,0,m[0,2]+m[1,3]+m[2,0]+m[2,4]);
		==
			SumOnD(m,5,2,3,1,m[0,2]+m[1,3]+m[2,0]+m[2,4]);
		==
			SumOnD(m,5,2,3,2,m[0,2]+m[1,3]+m[2,0]+m[2,4]+m[3,1]);
		==
			SumOnD(m,5,2,3,3,m[0,2]+m[1,3]+m[2,0]+m[2,4]+m[3,1]);
		==
			SumOnD(m,5,2,3,4,m[0,2]+m[1,3]+m[2,0]+m[2,4]+m[3,1]);
		==
			SumOnD(m,5,2,3,5,m[0,2]+m[1,3]+m[2,0]+m[2,4]+m[3,1]);
		==
			SumOnD(m,5,2,4,0,m[0,2]+m[1,3]+m[2,0]+m[2,4]+m[3,1]);
		==
			SumOnD(m,5,2,4,1,m[0,2]+m[1,3]+m[2,0]+m[2,4]+m[3,1]);
		==
			SumOnD(m,5,2,4,2,m[0,2]+m[1,3]+m[2,0]+m[2,4]+m[3,1]);
		==
			SumOnD(m,5,2,4,3,m[0,2]+m[1,3]+m[2,0]+m[2,4]+m[3,1]+m[4,2]);
		==
			SumOnD(m,5,2,4,4,m[0,2]+m[1,3]+m[2,0]+m[2,4]+m[3,1]+m[4,2]);
		==
			SumOnD(m,5,2,4,5,m[0,2]+m[1,3]+m[2,0]+m[2,4]+m[3,1]+m[4,2]);
		==
			SumOnD(m,5,2,5,0,m[0,2]+m[1,3]+m[2,0]+m[2,4]+m[3,1]+m[4,2]);
		==
			m[0,2]+m[1,3]+m[2,0]+m[2,4]+m[3,1]+m[4,2];
		==
			-2+17+2-3+0-2;
		==
			12;
		}
	}
}

function MatrixDiagSum(m: array2<int>, N: nat, d: nat): int
	requires m != null && d < N == m.Length0 == m.Length1
	reads m
{
	SumOnD(m, N, d, 0, 0, 0)
} 

function SumOnD(m: array2<int>, N: nat, d: nat, i: nat, j: nat, sum: int): int
	requires m != null && d < N == m.Length0 == m.Length1 && i <= N && j <= N
	decreases N-i, N-j
	reads m
{
	if i == N then sum else
	if j == N then SumOnD(m, N, d, i+1, 0, sum) else
	if Abs(i-j) == d then SumOnD(m, N, d, i, j+1, sum+m[i,j]) else
	SumOnD(m, N, d, i, j+1, sum)
}

function Abs(n: int): nat { if n>=0 then n else -n }



/** lemma Looper(m:array2<int>, N:nat, d:nat, i:nat, s:int)
	requires m != null && d < N == m.Length0 == m.Length1 && i <= N
	ensures MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s)
	{
	//s includes all the elements collected until we reach row k, k=i-1
	//we want to tell dafny that SummAll = SumOnD(m,N,d,i,0,s) 
	//meaning that the s we collected so far, + all the rest of the valid elements as identified and summed by SumOnD(m,N,d,i,0,s) 
	//is equal
	
	//How will Dafny understand this?
	//1. If i go over all the elements in the matrix until the row i, and for each element i will show that if i add it to s
	//   them it obides Abs(i-j)=d and if i don't take the element then Abs(i-j)!=d
	//   in the end i will have a new s that is the sum of all the valid(!) elements up to the current row.
	var k:int :=0;
	var sum:int :=0;
	while k<i
		invariant k <= i
		invariant MatrixDiagSum(m,N,d) == SumOnD(m,N,d,k,0,sum)
		decreases N-k
	   {
		var j:int :=0;
		while j!=N
			invariant j <= N
			invariant MatrixDiagSum(m,N,d) == SumOnD(m,N,d,k,j,sum)
			decreases N-j
		{
			if Abs(k-j) == d
			{
				sum := sum+m[k,j];
			}
			else
			{

			}
			j:=j+1;
		}
		k:=k+1;
	   }
	assert k==i;
	assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,k,0,sum);
	assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,sum);
	//assert s == sum;
	assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s);
	assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,sum);
	}

	*/

	lemma AbsLemma(m:array2<int>, N:nat, i:int, a:nat, b:nat, d:nat)
	requires m != null && d < N == m.Length0 == m.Length1 && i < N
	ensures forall x :: a <= x < b ==> Abs(i-x)!=d


 method MatrixDiagonal(m: array2<int>, N:nat, d:nat) returns (s:int)
	requires m!=null && d<N == m.Length0 == m.Length1
	ensures s==MatrixDiagSum(m,N,d)
	{
		s:=0;
		var i: int :=0;

		assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s);

		while i!=N
			invariant i<=N
			invariant MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s)
			decreases N-i
			{
				assert i<=N;
				assert i<N;
				
				if(i-d>=0){
					LooperRow(m,N,d,i,0,i-d,s);
					s:=s+m[i,i-d];
					if(i+d<N){
						assert m != null && d < N == m.Length0 == m.Length1 && i < N;
						assert 0<=i-d<=i+d<N;

						//AbsLemma(m,N,d,i,i-d+1,i+d);
						assert forall x :: i-d+1 <= x < i+d ==> Abs(i-x)!=d;
						assert i+d<N;
						assert i-d>=0;
						assert 0<=i-d+1<=i+d<N;
						//forall x | i-d <= x < i+d ensures Abs(i-x)!=d by { }
						LooperRow(m,N,d,i,i-d+1,i+d,s);
						s:=s+m[i,i+d];
						LooperRow(m,N,d,i,i+d+1,N,s);
						//In this case we should do 3 loops, one from 0 to i-d, one from i-d to i+d and one from i+d to N
					}
					else{
						LooperRow(m,N,d,i,i-d+1,N,s);
						//In this case we should do a loop from 0 to i-d and a loop from i-d to N
					}
			}
			else{
				if(i+d<N){
					LooperRow(m,N,d,i,0,i+d,s);
					s:=s+m[i,i+d];
					LooperRow(m,N,d,i,i+d+1,N,s);
						//In this case we should do a loop from 0 to i+d and a loop from i+d to N
				}
				else{
					LooperRow(m,N,d,i,0,N,s);
					//In this case we should do a loop from 0 to N
				}
			}
				
			
				assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i+1,0,s) by {}
				i:=i+1;
				assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s);
			}

		
			assert i==N;
		
			assert s == MatrixDiagSum(m,N,d);

	}

/**
method MatrixDiagonal(m: array2<int>, N: nat, d: nat) returns (s: int)
	requires m != null && d < N == m.Length0 == m.Length1
	ensures s == MatrixDiagSum(m,N,d)
{
	/*
		The following implementation makes N*N checks of "Abs(i-j) == d".
		Re-implement without any use of "Abs" (make it a simple "function", not a "function method").
		The challenge is to compute the sum of the relevant elements from each row directly,
		skipping all irrelevant elements.
	*/
	s := 0;
	var i: nat := 0;
	while i != N
		invariant i <= N
		invariant MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s)
		decreases N-i
	{
		var j: nat := 0;
		while j != N
			invariant j <= N
			invariant MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j,s)
			decreases N-j
		{
			if Abs(i-j) == d
			{
				s := s+m[i,j];
			}
			j := j+1;
		}
		i := i+1;
	}
}

method MatrixDiagonal'(m: array2<int>, N: nat, d: nat) returns (s: int)
	requires m != null && d < N == m.Length0 == m.Length1
	ensures s == MatrixDiagSum(m,N,d)
{
	s := 0;
	var i: nat := 0;
	while i != N
		invariant i <= N
		invariant MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s)
		decreases N-i
	{
		var j: nat := 0;
		while j != N
			invariant j <= N
			invariant MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j,s)
			decreases N-j
		{
			assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j,s);
			if Abs(i-j) == d
			{
				assert m != null && d < N;
				assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j,s);
				assert Abs(i-j) == d;
				assert i < N && j < N;
				// ==>
				assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j+1,s+m[i,j]);
				s := s+m[i,j];
				assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j+1,s);
			}
			else
			{
				assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j,s);
				assert Abs(i-j) != d;
				assert i < N && j < N;
				// ==>
				assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j+1,s);
			}
			assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j+1,s);
			j := j+1;
		}
		i := i+1;
	}
}
*/

lemma L1(m: array2<int>, N: nat, d: nat, i: nat, j: nat, s: int)
	// an irrelevant element a[i,j] (with "Abs(i-j) != d") can be skipped...
	requires m != null && d < N == m.Length0 == m.Length1
	requires i < N
	requires j < N
	requires Abs(i-j) != d 
	ensures SumOnD(m,N,d,i,j,s) == SumOnD(m,N,d,i,j+1,s)
{
	assert SumOnD(m,N,d,i,j,s) == SumOnD(m,N,d,i,j+1,s) by
	{
		assert i < N;
		assert j < N;
		assert d != Abs(i-j);
	}
}

lemma Looper(m:array2<int>, N:nat, d:nat, i:nat, s:int)
requires m!=null && d<N == m.Length0 == m.Length1 && i<N
ensures MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i+1,0,s)

// a and b refer to the start and end indexes of j meaning from m[i,a] to m[i,b] all elements m[i,k] 
// Abs(i-k)!=d
lemma LooperRow(m:array2<int>, N:nat, d:nat, i:nat, a:nat, b:nat, s:int)
requires m != null && d < N == m.Length0 == m.Length1 && i < N 
requires 0<=a<=b<N
requires forall x :: a <= x < b ==> Abs(i-x)!=d;
ensures SumOnD(m,N,d,i,a,s)== SumOnD(m,N,d,i,b,s)
{
	var k:=a;
	assert forall x :: a <= x < b ==> Abs(i-x)!=d;
	assert forall x :: a < x < b ==> Abs(i-x)!=d;

	while k!=b
		invariant a<=k<=b && SumOnD(m,N,d,i,a,s)==SumOnD(m,N,d,i,k,s)
	{	
		assert forall l:: a<=l<b ==> Abs(i-l)!=d;
		//assert Abs(i-k)!=d;
		assert m != null && d < N == m.Length0 == m.Length1 && i <N;
		assert a<=k+1<=b && SumOnD(m,N,d,i,a,s)==SumOnD(m,N,d,i,k+1,s) by 
		{
			assert m != null && d < N == m.Length0 == m.Length1 && i <= N;
			calc{
					SumOnD(m,N,d,i,a,s);
					== 
					SumOnD(m,N,d,i,k,s);
					== 
					{
						assert m != null && d < N == m.Length0 == m.Length1 && i <N;
						L1(m,N,d,i,k,s);
					}
					SumOnD(m,N,d,i,k+1,s);
				}	
		}
		k:=k+1;
		assert a<=k<=b && SumOnD(m,N,d,i,a,s)==SumOnD(m,N,d,i,k,s);
	}
	assert a<=k<=b && SumOnD(m,N,d,i,a,s)==SumOnD(m,N,d,i,k,s);
	assert k==b;
	assert SumOnD(m,N,d,i,a,s)== SumOnD(m,N,d,i,b,s);
}



lemma L2(m:array2<int>, N:nat, d:nat, i:nat, j:nat, s:int)
	requires m!=null && d<N==m.Length0 == m.Length1
	requires i<N
	requires j<N
	requires Abs(i-j)==d
	ensures SumOnD(m,N,d,i,j,s)== SumOnD(m,N,d,i,j+1,s+m[i,j])
	{
		assert SumOnD(m,N,d,i,j,s)==SumOnD(m,N,d,i,j+1,s+m[i,j]) by 
		{
			assert i<N;
			assert j<N;
			assert d==Abs(i-j);
		}
	}