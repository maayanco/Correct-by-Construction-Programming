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

lemma Looper(m:array2<int>, N:nat, d:nat, i:nat, s:int)
	requires m != null && d < N == m.Length0 == m.Length1 && i <= N
	ensures MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s)



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
					s:=s+m[i,i-d];

					if(i+d<N){
						s:=s+m[i,i+d];
						//increased s by 2 elements (i,i-d) and (i,i+d)
					}
					else{
						//increased s by 1 element (i,i-d)
					}
				}
				else{
					if(i+d<N){
						s:=s+m[i,i+d];
						//increased s by 1 element (i,i+d)
					}
					else{
						//s isn't changed
					}
				}

				assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i+1,0,s) by {Looper(m,N,d,i+1,s);}
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