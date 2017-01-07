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

				if(i-d>=0) //i-d>=0
				{	
					//covering the skippable gap between m[i,0] to m[i,i-d]
					assert SumOnD(m,N,d,i,0,s)==SumOnD(m,N,d,i,i-d,s) by {LooperRow(m,N,d,i,0,i-d,s);}
					//adding the element at m[i,i-d]
					assert SumOnD(m,N,d,i,i-d,s)==SumOnD(m,N,d,i,i-d+1,s+m[i,i-d]) by {L2(m,N,d,i,i-d,s);} 
					s:=s+m[i,i-d];
					if(i+d<N) //i-d>=0 and i+d<N
					{
						if(d==0) //meaning i-d==i+d, i-d>=0 and i+d<N
						{
							//covering the skippable gap between m[i,i-d+1] to m[i,N]
							assert d==0;
							assert SumOnD(m,N,d,i,i-d+1,s)==SumOnD(m,N,d,i,N,s) by {LooperRow(m,N,d,i,i-d+1,N,s);}
						}
						else //i-d>=0 and i+d<N and d!=0
						{
							//covering the skippable gap between m[i,i-d+1] to m[i,i-d+1,i+d]
							assert d!=0;
							assert SumOnD(m,N,d,i,i-d+1,s)==SumOnD(m,N,d,i,i+d,s) by {LooperRow(m,N,d,i,i-d+1,i+d,s);}

							//adding the element at m[i,i+d]
							assert SumOnD(m,N,d,i,i+d,s)==SumOnD(m,N,d,i,i+d+1,s+m[i,i+d]) by {L2(m,N,d,i,i+d,s);} 

							s:=s+m[i,i+d];

							//covering all the skippable gap between m[i,i+d+1] to m[i,N]
							assert SumOnD(m,N,d,i,i+d+1,s)==SumOnD(m,N,d,i,N,s) by {LooperRow(m,N,d,i,i+d+1,N,s);}					
						}
					}
					else //i-d>=0 and !(i+d<N)
					{
						//covering the skippable gap between m[i,i-d+1] to m[i,N]
						assert SumOnD(m,N,d,i,i-d+1,s)==SumOnD(m,N,d,i,N,s) by {LooperRow(m,N,d,i,i-d+1,N,s);}
					}
			}
			else // !(i-d>=0)
			{
				if(i+d<N){ // !(i-d>=0) and i+d<N
					//covering the skippable gap between m[i,0] to m[i,i+d]
					assert SumOnD(m,N,d,i,0,s)==SumOnD(m,N,d,i,i+d,s) by {LooperRow(m,N,d,i,0,i+d,s);}

					//adding the element at m[i,i+d] to s
					assert SumOnD(m,N,d,i,i+d,s)==SumOnD(m,N,d,i,i+d+1,s+m[i,i+d]) by {L2(m,N,d,i,i+d,s);} 

					s:=s+m[i,i+d];
					
					//covering the skipppable gap between m[i,i+d+1] to m[i,N]
					assert SumOnD(m,N,d,i,i+d+1,s)==SumOnD(m,N,d,i,N,s) by {LooperRow(m,N,d,i,i+d+1,N,s);}
						
				}
				else // !(i-d>=0) and !(i+d<N)
				{
					//covering the skippable gap between m[i,0] to m[i,N]
					assert SumOnD(m,N,d,i,0,s)==SumOnD(m,N,d,i,N,s) by {LooperRow(m,N,d,i,0,N,s);}
					
				}
			}
				
			assert i+1<=N &&MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i+1,0,s);
			i:=i+1;
			assert i<=N && MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s);
		}

		assert i==N && i<=N && MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s);
		// ==> {SumOnD(m,N,d,i,0,s) == SumOnD(m, N, d, N, 0, s) (because i==N) == s (by definition) }
		assert s == MatrixDiagSum(m,N,d);
		
	}

// a and b refer to the start and end indexes of j meaning from m[i,a] to m[i,b] 
//all elements m[i,k] ==> Abs(i-k)!=d
lemma LooperRow(m:array2<int>, N:nat, d:nat, i:nat, a:nat, b:nat, s:int)
requires m != null && d < N == m.Length0 == m.Length1 && i < N 
requires forall x:nat :: a <= x < b ==> (if (i-x)>=0 then (i-x) else -(i-x)) != d
requires  0<=a<=b<=N
ensures SumOnD(m,N,d,i,a,s)== SumOnD(m,N,d,i,b,s)
{	
	assert forall x:nat :: a <= x < b ==> (if (i-x)>=0 then (i-x) else -(i-x)) != d;
	var k:=a;
	while k!=b
		invariant a<=k<=b && SumOnD(m,N,d,i,a,s)==SumOnD(m,N,d,i,k,s)
	{	
		assert a<=k+1<=b && SumOnD(m,N,d,i,a,s)==SumOnD(m,N,d,i,k+1,s) by 
		{
			calc{
					SumOnD(m,N,d,i,a,s);
					== 
					SumOnD(m,N,d,i,k,s);
					== 
					{
						L1(m,N,d,i,k,s);
					}
					SumOnD(m,N,d,i,k+1,s);
				}	
		}
		k:=k+1;
	}
	assert k==b && a<=k<=b && SumOnD(m,N,d,i,a,s)==SumOnD(m,N,d,i,k,s);
	assert SumOnD(m,N,d,i,a,s)== SumOnD(m,N,d,i,b,s);
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


/** Annotated Versions (Inluding asserts) */

/**

method MatrixDiagonal'(m: array2<int>, N:nat, d:nat) returns (s:int)
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
				assert i!=N && i<=N;
				// ==>
				assert i<N;
				
				if(i-d>=0) //i-d>=0
				{	
					//covering the skippable gap between m[i,0] to m[i,i-d]
					assert i-d>=0;
					assert SumOnD(m,N,d,i,0,s)==SumOnD(m,N,d,i,i-d,s) by 
					{
						assert m != null && d < N == m.Length0 == m.Length1 && i < N;
						assert forall x:nat :: 0 <= x < i-d ==> Abs(i-x)!= d;
						assert  0<=0<=i-d<=N;
						LooperRow(m,N,d,i,0,i-d,s);
					}
					//adding the element at m[i,i-d]
					assert SumOnD(m,N,d,i,i-d,s)==SumOnD(m,N,d,i,i-d+1,s+m[i,i-d]) by 
					{
						assert m!=null && d<N==m.Length0 == m.Length1 && i<N && i-d<N;
						assert Abs(i-(i-d))==d;
						L2(m,N,d,i,i-d,s);
					} 
					s:=s+m[i,i-d];
					if(i+d<N) //i-d>=0 and i+d<N
					{
						assert i+d<N;
						if(d==0) //meaning i-d==i+d, i-d>=0 and i+d<N
						{
							//covering the skippable gap between m[i,i-d+1] to m[i,N]
							assert d==0;
							assert SumOnD(m,N,d,i,i-d+1,s)==SumOnD(m,N,d,i,N,s) by
							{	
								assert m != null && d < N == m.Length0 == m.Length1 && i < N  && i-d+1<=N && N<=N;
								assert 0<=i-d+1<=N<=N;
								assert forall x :: i-d+1 <= x < N ==> Abs(i-x)!=d;
								LooperRow(m,N,d,i,i-d+1,N,s);
							}
						}
						else //i-d>=0 and i+d<N and d!=0
						{
							//covering the skippable gap between m[i,i-d+1] to m[i,i-d+1,i+d]
							assert d!=0;
							assert SumOnD(m,N,d,i,i-d+1,s)==SumOnD(m,N,d,i,i+d,s) by 
							{	
								assert m != null && d < N == m.Length0 == m.Length1 && i < N  && i-d+1<=N && i+d<=N;
								assert 0<=i-d+1<=i+d<=N;
								assert forall x :: i-d+1 <= x < i+d ==> Abs(i-x)!=d; 
								LooperRow(m,N,d,i,i-d+1,i+d,s);
							}
							//adding the element at m[i,i+d]
							assert SumOnD(m,N,d,i,i+d,s)==SumOnD(m,N,d,i,i+d+1,s+m[i,i+d]) by 
							{
								assert m!=null && d<N==m.Length0 == m.Length1 && i<N && i+d<N;
								assert Abs(i-(i+d))==d;
								L2(m,N,d,i,i+d,s);
							} 
							s:=s+m[i,i+d];
							//covering all the skippable gap between m[i,i+d+1] to m[i,N]
							assert SumOnD(m,N,d,i,i+d+1,s)==SumOnD(m,N,d,i,N,s) by 
							{
								assert m != null && d < N == m.Length0 == m.Length1 && i < N  && i+d+1<=N && N<=N;
								assert 0<=i+d+1<=N<=N;
								assert forall x :: i+d+1 <= x < N ==> Abs(i-x)!=d;
								LooperRow(m,N,d,i,i+d+1,N,s);
							}					
						}
					}
					else //i-d>=0 and !(i+d<N)
					{
						//covering the skippable gap between m[i,i-d+1] to m[i,N]
						assert SumOnD(m,N,d,i,i-d+1,s)==SumOnD(m,N,d,i,N,s) by 
						{
							assert m != null && d < N == m.Length0 == m.Length1 && i < N  && i-d+1<=N && N<=N;
							assert 0<=i-d+1<=N<=N;
							assert forall x :: i-d+1 <= x < N ==> Abs(i-x)!=d;
							LooperRow(m,N,d,i,i-d+1,N,s);
						}
					}
			}
			else // !(i-d>=0)
			{
				if(i+d<N){ // !(i-d>=0) and i+d<N
					//covering the skippable gap between m[i,0] to m[i,i+d]
					assert SumOnD(m,N,d,i,0,s)==SumOnD(m,N,d,i,i+d,s) by 
					{
						assert m != null && d < N == m.Length0 == m.Length1 && i < N  && 0<=N && i+d<=N;
						assert 0<=0<=i+d<=N;
						assert forall x :: 0 <= x < i+d ==> Abs(i-x)!=d;
						LooperRow(m,N,d,i,0,i+d,s);
					}

					//adding the element at m[i,i+d] to s
					assert SumOnD(m,N,d,i,i+d,s)==SumOnD(m,N,d,i,i+d+1,s+m[i,i+d]) by 
					{
						assert m!=null && d<N==m.Length0 == m.Length1 && i<N && i+d<N;
						assert Abs(i-(i+d))==d;
						L2(m,N,d,i,i+d,s);
					} 

					s:=s+m[i,i+d];
					
					//covering the skipppable gap between m[i,i+d+1] to m[i,N]
					assert SumOnD(m,N,d,i,i+d+1,s)==SumOnD(m,N,d,i,N,s) by 
					{
						assert m != null && d < N == m.Length0 == m.Length1 && i < N  && i+d+1<=N && N<=N;
						assert 0<=i+d+1<=N<=N;
						assert forall x :: i+d+1 <= x < N ==> Abs(i-x)!=d;
						LooperRow(m,N,d,i,i+d+1,N,s);
					}
						
				}
				else // !(i-d>=0) and !(i+d<N)
				{
					//covering the skippable gap between m[i,0] to m[i,N]
					assert SumOnD(m,N,d,i,0,s)==SumOnD(m,N,d,i,N,s) by 
					{
						assert m != null && d < N == m.Length0 == m.Length1 && i < N  && 0<=N && N<=N;
						assert 0<=0<=N<=N;
						assert forall x :: 0 <= x < N ==> Abs(i-x)!=d;
						LooperRow(m,N,d,i,0,N,s);
					}
					
				}
			}
				
			assert i+1<=N &&MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i+1,0,s);
			i:=i+1;
			assert i<=N && MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s);
		}

		assert i==N && i<=N && MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s);
		// ==> {SumOnD(m,N,d,i,0,s) == SumOnD(m, N, d, N, 0, s) (because i==N) == s (by definition) }
		assert s == MatrixDiagSum(m,N,d);
		
	}
	


// a and b refer to the start and end indexes of j meaning from m[i,a] to m[i,b] 
//every element m[i,k] ==> Abs(i-k)!=d
lemma LooperRow'(m:array2<int>, N:nat, d:nat, i:nat, a:nat, b:nat, s:int)
requires m != null && d < N == m.Length0 == m.Length1 && i < N 
requires forall x:nat :: a <= x < b ==> (if (i-x)>=0 then (i-x) else -(i-x)) != d
requires  0<=a<=b<=N
ensures SumOnD(m,N,d,i,a,s)== SumOnD(m,N,d,i,b,s)
{	
	assert m != null && d < N == m.Length0 == m.Length1 && i < N;
	assert forall x:nat :: a <= x < b ==> (if (i-x)>=0 then (i-x) else -(i-x)) != d;
	assert 0<=a<=b<=N;

	var k:=a;

	while k!=b
		invariant a<=k<=b && SumOnD(m,N,d,i,a,s)==SumOnD(m,N,d,i,k,s)
	{	
		assert a<=k+1<=b && SumOnD(m,N,d,i,a,s)==SumOnD(m,N,d,i,k+1,s) by 
		{
			calc
			{
					SumOnD(m,N,d,i,a,s);
					== 
					{
						assert SumOnD(m,N,d,i,a,s)==SumOnD(m,N,d,i,k,s);
					}
					SumOnD(m,N,d,i,k,s);
					== 
					{
						assert m != null && d < N == m.Length0 == m.Length1 && i < N && k < N;
						assert Abs(i-k) != d;
						L1(m,N,d,i,k,s);
						assert SumOnD(m,N,d,i,k,s) == SumOnD(m,N,d,i,k+1,s);
					}
					SumOnD(m,N,d,i,k+1,s);
				}	
		}

		k:=k+1;
		assert a<=k<=b && SumOnD(m,N,d,i,a,s)==SumOnD(m,N,d,i,k,s);
	}
	assert k==b && a<=k<=b && SumOnD(m,N,d,i,a,s)==SumOnD(m,N,d,i,k,s);
	// ==>
	assert SumOnD(m,N,d,i,a,s)== SumOnD(m,N,d,i,b,s);
}

*/