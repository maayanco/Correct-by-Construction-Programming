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

/**lemma ShwoopDeLoop(m: array2<int>, N:nat, d:nat, i:nat, j:nat, s:int)
	requires m != null && d < N == m.Length0 == m.Length1 && i <= N && j <= N
	ensures MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j,s)
	{
		assert (MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j,s)) ==> (MatrixDiagSum(m,N,d) == s + SumOnD(m,N,d,i,j,0) ) ; 
	}
	*/
	/**
lemma Looper(m: array2<int>, N:nat, d:nat, i:nat, j:nat, s:int)
	requires m!=null &&d<N==m.Length0 == m.Length1
	requires i<=N
	requires j<N
	ensures MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j,s)
	//I want to say that SumOnD(m,N,d,i,j,s) is equal to the s we would receive if we summed up all the correct values up to m[i,j]
	//plus SumOnD(m,N,d,i,j,0)
	{
	var s':nat;
	s':=0;
		//for all k,l:nat | k>=0 && l>=0 && k<=i && k<j ensures SumOnD(m,n,d,i,j,s) == MatrixDiagSum(m,N,d)
		
		//here i really want to go over all the elements, and say that 
		forall k,l:nat | k>=i && l>=j && k<N && l<N ensures MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s')
		{
			if(Abs(k-l)==d){
				assert Abs(k-l)==d;
				L2(m,N,d,k,l,s);
				assert SumOnD(m,N,d,k,l,s)== SumOnD(m,N,d,k,l+1,s+m[k,l]);
			}
			else{
				assert Abs(k-l)!=d;
				L1(m,N,d,k,l,s);
				assert SumOnD(m,N,d,k,l,s) == SumOnD(m,N,d,k,l+1,s);
			}
		} 
	}*/



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

method max(a: int, b: int) returns (s:int)
{
	//s:=0;
	if a > b{	
		s:=a;
	} 
	else{
		s:=b;
   }
}

method MatrixDiagonal(m: array2<int>, N:nat, d:nat) returns (s:int)
	requires m!=null && d<N == m.Length0 == m.Length1
	ensures s==MatrixDiagSum(m,N,d)
	{
	
	s:=0;
	//ghost var s':=s;
	var i: int :=0;
	assert m!=null && d<N == m.Length0 == m.Length1;
	assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s);
	assert s == MatrixDiagSum(m,N,d) - SumOnD(m,N,d,i,0,0);

	while i!=N
		invariant i<=N
		//what do i want to say?? i want to say that the sum i have accumulated so far, s,
		//plus the rest of the valid elements in the array SumOnD(m,N,d,i,j,s) will be equal to the end result MatrixDiagSum(m,N,d)
		//invariant MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s)
		//invariant s == MatrixDiagSum(m,N,d) - SumOnD(m,N,d,i,0,0)
		decreases N-i
		{
			assert i<=N;
			assert i<N;
			//assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s) by {Looper(m,N,d,i,0,s);}
			//s':=s;

			if(i-d-1>=0){
				forall j:int | 0<=j<i-d  && i>d ensures SumOnD(m,N,d,i,j,s)==SumOnD(m,N,d,i,i-d-1,s) {L1(m,N,d,i,j,s);}
				assert SumOnD(m,N,d,i,0,s)==SumOnD(m,N,d,i,i-d-1,s); 
			}

			ghost var maxValidJ:=max(0,i-d-1);
			forall j:int | 0<=j<i-d  && i>d ensures SumOnD(m,N,d,i,j,s)==SumOnD(m,N,d,i,j+1,s) {
				L1(m,N,d,i,j,s);
			}
			assert SumOnD(m,N,d,i,0,s)==SumOnD(m,N,d,i,maxValidJ,s); 

			//forall k:nat | 0<=k<d-i && i-k>=0 && i-k>d ensures SumOnD(m,N,d,i,0,s)==SumOnD(m,N,d,i,k,s) {L1(m,N,d,i,k,s);}

			if(i-d>=0){
				s:=s+m[i,i-d];

				if(i+d<N){
					s:=s+m[i,i+d];
				}
				else{
					
				}
			}
			else{
				//Took nothing so far..
				if(i+d<N){
					s:=s+m[i,i+d];
				}
				else{
				}
			}

			forall k:nat | 0<=k<d+i && i-k<N && i-k>=0 && i-k<d ensures SumOnD(m,N,d,i,0,s)==SumOnD(m,N,d,i,k,s) {L1(m,N,d,i,k,s);}

			i:=i+1;

		}

		
		assert i==N;
		//assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,N,s); //by { LoopingLemma(m,N,d,i,s); }
		assert s == MatrixDiagSum(m,N,d);

	}

	method MatrixDiagonal2(m: array2<int>, N:nat, d:nat) returns (s:int)
	requires m!=null && d<N == m.Length0 == m.Length1
	ensures s==MatrixDiagSum(m,N,d)
	{
	s:=0;
	var i: int :=0;
	assert m!=null && d<N == m.Length0 == m.Length1;
	assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s);

	assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s);
	while i!=N
		invariant i<=N
		invariant MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s)
		decreases N-i
		{
			assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s);
			assert i<N;
			if(i+d<N){
				//	forall k:nat ensures 0<=k && k<=i+d { L1(m,N,d,i,i+d,s);}
				assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s);
				s:=s+m[i,i+d];
				assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s-m[i,i+d]);
				if(i-d>=0){
					assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s-m[i,i+d]);
					s:=s+m[i,i-d];
					assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s-m[i,i+d]-m[i,i-d]);
				}
				else{
					assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s-m[i,i+d]);
				}
			}
			else{
				//assert i+d >=N;
				//assert m != null && d < N == m.Length0 == m.Length1 && i <= N && i+d <= N;
				//assert SumOnD(m,N,d,i,i+d,s) == SumOnD(m,N,d,i,i+d,s);
				assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s);
				if(i-d>=0){
					assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s);
					s:=s+m[i,i-d];
					assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s-m[i,i-d]);
				}
				else{
					assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s);
				}
				//in one case we added an element to s and in the other we didn't..
				//i need to tell dafny that all the other elements in this row definately don't need to be added to the sum s
				assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,N-1,s);

				assert (MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s-m[i,i-d])) || (MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s-m[i,i-d]));
			}

			assert (MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s-m[i,i-d])) || (MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s)) || (MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s-m[i,i+d])) || (MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s-m[i,i+d]-m[i,i-d]));

			i:=i+1;
				assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s);
		}

		assert i==N;
		assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s);
		assert s == MatrixDiagSum(m,N,d);

	}



/** method MatrixDiagonal(m: array2<int>, N: nat, d: nat) returns (s: int)
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
}*/


