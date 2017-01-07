method Main() {
	var str1,str2 := "Dafny","fn";
	var found,offset := FindSubstring(str1,str2);
	assert found by
	{
		calc {
			str2 <= str1[2..];
		==>
			IsSubsequenceAtOffset(str1,str2,2);
		==>
			IsSubsequence(str1,str2);
		==
			found;
		}
	}
	assert offset == 2 by
	{
		assert found && str2 <= str1[2..];
		assert offset != 0 by { assert 'D' == str1[0] != str2[0] == 'f'; }
		assert offset != 1 by { assert 'a' == str1[1] != str2[0] == 'f'; }
		assert offset != 3 by { assert 'n' == str1[3] != str2[0] == 'f'; }
		assert !(offset >= 4) by { assert 4 + |str2| > |str1|; }
	}
	print "The sequence ";
	print str2;
	print " is a subsequence of ";
	print str1;
	print " starting at element ";
	print offset;
}

predicate IsSubsequence<T>(q1: seq<T>, q2: seq<T>)
{
	exists offset: nat :: offset + |q2| <= |q1| && IsSubsequenceAtOffset(q1,q2,offset)
}

predicate IsSubsequenceAtOffset<T>(q1: seq<T>, q2: seq<T>, offset: nat)
{ // "<=" on sequences means "is prefix?": "is q2 a prefix of q1[offset..]"
	offset + |q2| <= |q1| && q2 <= q1[offset..]
}


method FindSubstring(str1: string, str2: string) returns (found: bool, offset: nat)
	// a string in Dafny is a sequence of characters: "seq<char>"
	ensures found <==> IsSubsequence(str1,str2)
	ensures found ==> IsSubsequenceAtOffset(str1,str2,offset)
{
	offset := 0;
	found := ((offset + |str2|) <= |str1|) && (str2 <= str1);

	while ( offset + |str2| <= |str1| && !found )
	invariant found <==> IsSubsequenceAtOffset(str1,str2,offset)
	invariant (exists i: nat :: i < offset  && IsSubsequenceAtOffset(str1,str2,i)) ==> found
	decreases |str1|-offset
	{
		offset := offset+1;
		found := ( (offset + |str2|) <= |str1|) && str2 <= str1[offset..];
	}

	assert found <==> IsSubsequenceAtOffset(str1,str2,offset);
	assert (exists i: nat :: i < offset  && IsSubsequenceAtOffset(str1,str2,i)) ==> found;

	assert found <==> IsSubsequence(str1,str2);
	assert found ==> IsSubsequenceAtOffset(str1,str2,offset);
}



/**  Annotated Version: */

/**
method FindSubstring'(str1: string, str2: string) returns (found: bool, offset: nat)
	// a string in Dafny is a sequence of characters: "seq<char>"
	ensures found <==> IsSubsequence(str1,str2)
	ensures found ==> IsSubsequenceAtOffset(str1,str2,offset)
{
	
	assert (((0 + |str2|) <= |str1|) && (str2 <= str1)) <==> IsSubsequenceAtOffset(str1,str2,0);
	assert (exists i: nat :: i < 0  && IsSubsequenceAtOffset(str1,str2,i)) ==> (((0 + |str2|) <= |str1|) && (str2 <= str1));

	offset := 0;
	found := ((offset + |str2|) <= |str1|) && (str2 <= str1);

	assert found <==> IsSubsequenceAtOffset(str1,str2,offset);
	assert (exists i: nat :: i < offset  && IsSubsequenceAtOffset(str1,str2,i)) ==> found;

	while ( offset + |str2| <= |str1| && !found )
	invariant found <==> IsSubsequenceAtOffset(str1,str2,offset)
	invariant (exists i: nat :: i < offset  && IsSubsequenceAtOffset(str1,str2,i)) ==> found
	decreases |str1|-offset
	{
		assert ( offset + |str2| <= |str1| && !found ); //guard

		assert (( (offset+1 + |str2|) <= |str1|) && str2 <= str1[offset+1..]) <==> IsSubsequenceAtOffset(str1,str2,offset+1);
		assert (exists i: nat :: i < offset+1  && IsSubsequenceAtOffset(str1,str2,i)) ==> (( (offset+1 + |str2|) <= |str1|) && str2 <= str1[offset+1..]);

		offset := offset+1;
		
		assert (( (offset + |str2|) <= |str1|) && str2 <= str1[offset..]) <==> IsSubsequenceAtOffset(str1,str2,offset);
		assert (exists i: nat :: i < offset  && IsSubsequenceAtOffset(str1,str2,i)) ==> (( (offset + |str2|) <= |str1|) && str2 <= str1[offset..]);

		found := ( (offset + |str2|) <= |str1|) && str2 <= str1[offset..];
		
		assert found <==> IsSubsequenceAtOffset(str1,str2,offset);
		assert (exists i: nat :: i < offset  && IsSubsequenceAtOffset(str1,str2,i)) ==> found;
	}
	assert !( offset + |str2| <= |str1| && !found );
	assert (offset + |str2| > |str1|) || found; // equivilant

	//the invariants:
	assert found <==> IsSubsequenceAtOffset(str1,str2,offset);
	assert (exists i: nat :: i < offset  && IsSubsequenceAtOffset(str1,str2,i)) ==> found;

	// ==>

	assert found <==> IsSubsequence(str1,str2); // by LemaExplain(str1,str2,found,offset)
	assert found ==> IsSubsequenceAtOffset(str1,str2,offset); //by inv1 {found <==> IsSubsequenceAtOffset(str1,str2,offset);}
}

// The sole purpose of this lemma is to explain to the reader how the post condition is derived from the specified pre conditions
// It isn't a necessary part of our solution
// the preconditions are the !guard of the while loop and the invariants
// the postcondition of this lemma is one of the postconditions of the method FindSubstring
lemma LemmaExplain(str1: string, str2: string, found:bool, offset: nat)
requires !(offset + |str2| <= |str1| && !found)
requires found <==> IsSubsequenceAtOffset(str1,str2,offset)
requires (exists i: nat :: i < offset  && IsSubsequenceAtOffset(str1,str2,i)) ==> found
ensures found <==> IsSubsequence(str1,str2)
{

	assert (found <==> IsSubsequence(str1,str2))  == (found <==> (exists offset: nat :: offset + |str2| <= |str1| && IsSubsequenceAtOffset(str1,str2,offset)));
	
	assert found <== (exists offset: nat :: offset + |str2| <= |str1| && IsSubsequenceAtOffset(str1,str2,offset)); // equivilant to inv2 

	assert found ==> (exists offset: nat :: offset + |str2| <= |str1| && IsSubsequenceAtOffset(str1,str2,offset)) by
	{
		assert found ==> IsSubsequenceAtOffset(str1,str2,offset); //inv1
		assert (found ==> offset + |str2| <= |str1| && str2 <= str1[offset..]) ==> (found ==> (exists offset: nat :: offset + |str2| <= |str1| && IsSubsequenceAtOffset(str1,str2,offset)));
	}

	// ==> 

	assert found <==> IsSubsequence(str1,str2);

}

*/