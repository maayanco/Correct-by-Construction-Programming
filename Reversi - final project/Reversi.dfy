datatype Disk = White | Black
type Board = map<Position,Disk>
type Position = (int,int)
datatype Direction = Up | UpRight | Right | DownRight | Down | DownLeft | Left | UpLeft 

method Main()
{
	var board: Board := InitBoard();
	var player: Disk := Black;
	var legalMoves := FindAllLegalMoves(board, player);
	assert |legalMoves| > 0 by
	{
		// evidence that there are legal moves to begin with
		assert InitState(board);
		LemmaInitBlackHasLegalMoves(board);
		assert LegalMove(board, Black, (3,2));
		assert (3,2) in AllLegalMoves(board, Black);
	}
	while |legalMoves| != 0
		invariant ValidBoard(board) && (player == Black || player == White)
		invariant legalMoves == AllLegalMoves(board, player)
		invariant |legalMoves| == 0 <==> AllLegalMoves(board, Black) == AllLegalMoves(board, White) == {}
		decreases AvailablePositions(board)
	{
		var move;
		if player == Black
		{
			assert ValidBoard(board) && legalMoves <= AllLegalMoves(board, Black);
			assert forall pos :: pos in legalMoves <==> LegalMove(board,Black,pos);
			assert legalMoves != {};
			move := SelectBlackMove(board, legalMoves);
		}
		else
		{
			assert ValidBoard(board) && legalMoves <= AllLegalMoves(board, White);
			assert forall pos :: pos in legalMoves <==> LegalMove(board,White,pos);
			assert legalMoves != {};
			move := SelectWhiteMove(board, legalMoves);
		}
		PrintMoveDetails(board, player, move);
		board := PerformMove(board, player, move);
		player := if player == Black then White else Black;
		legalMoves := FindAllLegalMoves(board, player);
		if |legalMoves| == 0
		{
			// the current player has no legal move to make so the turn goes back to the opponent
			player := if player == White then Black else White;
			legalMoves := FindAllLegalMoves(board, player);
		}
	}
	assert AllLegalMoves(board, Black) == AllLegalMoves(board, White) == {};
	var blacks, whites := TotalScore(board);
	PrintResults(blacks, whites);
}


method PrintMoveDetails(board: Board, player: Disk, move: Position)
	requires ValidBoard(board) && LegalMove(board, player, move)
{
	print "\n", player, " is placed on row ", move.0, " and column ", move.1;
	var reversibleDirections := FindAllLegalDirectionsFrom(board, player, move);
	print " with reversible directions ", reversibleDirections;
	var reversiblePositions := FindAllReversiblePositionsFrom(board, player, move);
	print " and reversible positions ", reversiblePositions;
}

method PrintResults(blacks: nat, whites: nat)
{
	print "\nGame Over.\nAnd the winner is... ";
	print if blacks > whites then "The Black." else if blacks < whites then "The White." else "it's a tie.";
	print "\nFinal Score: ", blacks, " Black disks versus ", whites, " White disks.";
}

predicate ValidBoard(b: Board)
{
	forall pos :: pos in b ==> ValidPosition(pos)
}

function method ValidPositions(): set<Position>
{
	{
		(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),
		(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),
		(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),
		(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),
		(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),
		(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),
		(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),
		(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7)
	}
}

function method ValidDirection(): set<Direction>
{
	{
	Up , UpRight , Right , DownRight , Down , DownLeft , Left , UpLeft
	}
}

predicate ValidPosition(pos: Position)
{
	pos in ValidPositions()
}

predicate AvailablePosition(b: Board, pos: Position)
	requires ValidBoard(b)
{
	ValidPosition(pos) && pos !in b
}

method isAvailablePosition(b: Board, pos: Position) returns (ans: bool)
	requires ValidBoard(b)
	ensures ans == AvailablePosition(b, pos)
	{
		ans:= pos in ValidPositions() && pos !in b;
	}

predicate OccupiedPosition(b: Board, pos: Position)
	requires ValidBoard(b)
{
	ValidPosition(pos) && pos in b
}

predicate OccupiedBy(b: Board, pos: Position, player: Disk)
	requires ValidBoard(b)
{
	OccupiedPosition(b, pos) && b[pos] == player
}
method isOccupiedBy(b: Board, pos: Position, player: Disk) returns (ans: bool)
	requires ValidBoard(b)
	ensures ans == OccupiedBy(b, pos, player)
	{
		ans:= (pos in ValidPositions()) && pos in b && b[pos] == player;
	}

function AvailablePositions(b: Board): set<Position>
	requires ValidBoard(b)
{
 
	set pos | pos in ValidPositions() && AvailablePosition(b, pos)
}

method isAvailablePositions(b: Board) returns (positions: set<Position> )
requires ValidBoard(b)
ensures positions == AvailablePositions(b)
{
	positions:= {};
	var helper := (set pos | pos in ValidPositions());
	
 	while(|helper| > 0)
	decreases |helper|
	invariant forall pos :: pos in positions ==> AvailablePosition(b, pos)
	invariant forall pos :: pos in positions ==> pos in ValidPositions()
	invariant forall pos :: pos in helper ==> pos in ValidPositions()
	invariant forall pos:: pos in AvailablePositions(b) ==> pos in positions + helper
	{
		var pos :| pos in helper;
		var valisPos? := isAvailablePosition(b,pos);
		if(valisPos?)
		{
			positions := positions + {pos};
		}
		else
		{
		}
		helper := helper - {pos};
	}

}

function PlayerPositions(b: Board, player: Disk): set<Position>
	requires ValidBoard(b)
{
	set pos | pos in ValidPositions() && OccupiedBy(b, pos, player)
}

function Count(b: Board, player: Disk): nat
	requires ValidBoard(b)
{
	|PlayerPositions(b,player)|
}

predicate LegalMove(b: Board, player: Disk, pos: Position)
	requires ValidBoard(b)
{
	AvailablePosition(b, pos)	&&
	exists direction: Direction :: ReversibleVectorFrom(b, player, pos, direction)
}

method isReversibleVectorFrom(b: Board, player: Disk, move: Position, direction: Direction) returns (ans: bool)
	requires ValidBoard(b) && ValidPosition(move)
	ensures ans==ReversibleVectorFrom(b, player, move, direction)
	{
		var vector := CreatVectorPositionsFrom(move, direction);
		ans:= IsReversibleVector(b, vector, player);
	}

method isLegalMove(b: Board, player: Disk, pos: Position) returns (ans:bool)
 requires ValidBoard(b)
 ensures ans == LegalMove(b, player, pos)
 {
	ans:= false;
	var a := isAvailablePosition(b,pos);
	var b := exReversibleVectorFrom(b, player, pos);
	ans := a && b;
}

method exReversibleVectorFrom(b: Board, player: Disk, pos: Position) returns (ans:bool)
 requires ValidBoard(b)
 ensures ans <==> (ValidPosition(pos) && (exists direction: Direction :: ReversibleVectorFrom(b, player, pos, direction)))
 {
	var a := pos in ValidPositions();
	if (a)
	{
		var helper := (set direction | direction in ValidDirection());
		assume forall dir :: ReversibleVectorFrom(b, player, pos, dir) ==> dir in ValidDirection();
		ans := false;

		while (|helper|>0 && !ans)
		decreases |helper|
		invariant ans ==> (exists direction: Direction :: ReversibleVectorFrom(b, player, pos, direction))
		invariant exists direction: Direction :: ReversibleVectorFrom(b, player, pos, direction) ==> (ans || direction in helper)
		{
			var dir :| dir in helper;
			ans := isReversibleVectorFrom(b, player, pos, dir);
			helper:= helper - {dir};
		}
		assert  exists direction: Direction :: ReversibleVectorFrom(b, player, pos, direction) ==> (ans || direction in helper);
		assert exists direction: Direction :: ReversibleVectorFrom(b, player, pos, direction) ==> ans;
		assume  (exists direction: Direction :: ReversibleVectorFrom(b, player, pos, direction) ==> ans) ==> 
		(ans <== exists direction: Direction :: ReversibleVectorFrom(b, player, pos, direction));
		assert ans <== exists direction: Direction :: ReversibleVectorFrom(b, player, pos, direction);
		assert ans ==> (exists direction: Direction :: ReversibleVectorFrom(b, player, pos, direction));
		assert ans <==> (exists direction: Direction :: ReversibleVectorFrom(b, player, pos, direction));
	}
	else 
	{
		ans := false;
	}
 }
 
function Opponent(player: Disk): Disk
{
	if player == White then Black else White
}
method myOpponent(player: Disk) returns (ans: Disk)
ensures ans == Opponent(player)
{
	if (player == White)
	{
		ans:= Black;
	}
	else
	{
		ans:=White;
	}
}

function AllLegalMoves(b: Board, player: Disk): set<Position>
	requires ValidBoard(b)
{
	set move: Position | move in AvailablePositions(b) && LegalMove(b, player, move)
}

function ReversiblePositionsFrom(b: Board, player: Disk, move: Position): set<Position>
	requires ValidBoard(b)
{
	var reversibleDirections: set<Direction> := ReversibleDirections(b, player, move);
	set pos | pos in ValidPositions() && exists d :: d in reversibleDirections && pos in ReversibleVectorPositions(b, player, move, d)
}

function ReversibleDirections(b: Board, player: Disk, move: Position): set<Direction>
	requires ValidBoard(b)
	ensures var result := ReversibleDirections(b, player, move); forall dir :: dir in result ==> ReversibleVectorFrom(b, player, move, dir)
{
	if !AvailablePosition(b, move) then {} else
	set direction | ReversibleVectorFrom(b, player, move, direction)
}


predicate ReversibleVectorFrom(b: Board, player: Disk, move: Position, direction: Direction)
	requires ValidBoard(b) && ValidPosition(move)
{
	var vector := VectorPositionsFrom(move, direction);
	ReversibleVector(b, vector, player)
}


predicate ReversibleVector(b: Board, vector: seq<Position>, player: Disk)
	requires ValidBoard(b)
	requires forall pos :: pos in vector ==> ValidPosition(pos)
{
	|vector| >= 3 && AvailablePosition(b, vector[0]) &&
	exists j: nat :: 1 < j < |vector| && OccupiedBy(b, vector[j], player) && 
		forall i :: 0 < i < j ==> OccupiedBy(b, vector[i], Opponent(player))
}

// TODO -lemma from this method
method IsReversibleVector(b: Board, vector: seq<Position>, player: Disk) returns (ans: bool)
	requires ValidBoard(b) //&& |vector| > 0 && LegalMove(b, player, vector[0])
	requires forall pos :: pos in vector ==> ValidPosition(pos)
	ensures ans <==> ReversibleVector(b,vector,player)
{
	var opponent : Disk:=myOpponent(player);
	ans :=
	 |vector| >= 3 && 
		vector[0] !in b && vector[0] in ValidPositions() &&
	exists j: nat :: 1 < j < |vector| && vector[j] in ValidPositions() && vector[j] in b && b[vector[j]] == player &&
		forall i :: 0 < i < j ==> vector[i] in ValidPositions() && vector[i] in b && b[vector[i]] == opponent;
	assert ans ==> |vector| >= 3;
	assert ans ==> vector[0] !in b && vector[0] in ValidPositions();
	assert ans ==> exists j: nat :: 1 < j < |vector| && vector[j] in ValidPositions() && vector[j] in b && b[vector[j]] == player &&
		forall i :: 0 < i < j ==> vector[i] in ValidPositions() && vector[i] in b && b[vector[i]] == opponent;
	assert ReversibleVector(b,vector,player) ==> exists j: nat :: 1 < j < |vector| && vector[j] in ValidPositions() && vector[j] in b && b[vector[j]] == player &&
		forall i :: 0 < i < j ==> vector[i] in ValidPositions() && vector[i] in b && b[vector[i]] == opponent by{
			assert forall i :: 0 < i < |vector| ==> OccupiedBy(b, vector[i], player) == (vector[i] in ValidPositions() && vector[i] in b && b[vector[i]] == player);
		}
	assert ReversibleVector(b,vector,player) ==> |vector| >= 3;
	assert ReversibleVector(b,vector,player) ==> vector[0] !in b && vector[0] in ValidPositions();
	assert ans <== ReversibleVector(b,vector,player);
	assert ans ==> ReversibleVector(b,vector,player);
	assert ans <==> ReversibleVector(b,vector,player);
}

function ReversibleVectorPositions(b: Board, player: Disk, move: Position, direction: Direction): set<Position>
	requires ValidBoard(b) && ValidPosition(move)
	requires ReversibleVectorFrom(b, player, move, direction)
{ // collect the positions of all disks in the vector starting in the second position and ending before the first position occupied by an opponent
	var opponent := Opponent(player);
	var dummyPosition := (0,0);
	var positionsVector := VectorPositionsFrom(move, direction)+[dummyPosition,dummyPosition,dummyPosition,dummyPosition,dummyPosition]; // adding dummy disks to avoid (irrelevant) index out of range errors
	var firstCurrentPlayerDiskDistance :=
		if OccupiedBy(b, positionsVector[2], player) then 2
		else if OccupiedBy(b, positionsVector[3], player) then 3
		else if OccupiedBy(b, positionsVector[4], player) then 4
		else if OccupiedBy(b, positionsVector[5], player) then 5
		else if OccupiedBy(b, positionsVector[6], player) then 6
		else /* here must be OccupiedBy(b, positionsVector[7], player) */ 7;
	// skipping the first; collecting at least one position
	set pos | pos in positionsVector[1..firstCurrentPlayerDiskDistance]
}

method CreateReversibleVectorPositions(b: Board, player: Disk, move: Position, direction : Direction) returns (ans :set<Position>)
	requires ValidBoard(b) && ValidPosition(move)
	requires ReversibleVectorFrom(b, player, move, direction)
	ensures ans == ReversibleVectorPositions(b,player,move,direction)
{
		assert ValidBoard(b) && ValidPosition(move);
		var opponent : Disk := myOpponent(player);
		var dummyPosition := (0,0);
		var positionsVector : seq<Position> := CreatVectorPositionsFrom(move,direction);
		positionsVector := positionsVector + [dummyPosition,dummyPosition,dummyPosition,dummyPosition,dummyPosition]; 

		//write a loop that will find the first element that is 
		var cutPositionsVector : seq<Position>;
		
		var occupied2,occupied3,occupied4,occupied5,occupied6 : bool;
		occupied2 := isOccupiedBy(b,positionsVector[2],player);
		occupied3 := isOccupiedBy(b,positionsVector[3],player);
		occupied4 := isOccupiedBy(b,positionsVector[4],player);
		occupied5 := isOccupiedBy(b,positionsVector[5],player);
		occupied6 := isOccupiedBy(b,positionsVector[6],player);

		if occupied2
		{
			cutPositionsVector := positionsVector[1..2];
		}
		else if occupied3
		{
			cutPositionsVector := positionsVector[1..3];
		}
		else if occupied4
		{
			cutPositionsVector := positionsVector[1..4];
		}
		else if occupied5
		{
			cutPositionsVector := positionsVector[1..5];
		}
		else if occupied6
		{
			cutPositionsVector := positionsVector[1..6];
		}
		else
		{
			cutPositionsVector := positionsVector[1..7];
		}	
		
		ans := (set pos | pos in cutPositionsVector);

		//assert forall pos :: pos in ans ==> pos in b;

	    //assert OccupiedBy(b, positionsVector[2], player) ==> ans == (set pos | pos in VectorPositionsFrom(move, direction)[1..2]);
		assert ans == ReversibleVectorPositions(b,player,move,direction);
}

function VectorPositionsFrom(pos: Position, dir: Direction): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsFrom(pos, dir);
		forall pos :: pos in result ==> ValidPosition(pos)
{
	match dir {
		case Up        => VectorPositionsUpFrom(pos)
		case UpRight   => VectorPositionsUpRightFrom(pos)
		case Right     => VectorPositionsRightFrom(pos)
		case DownRight => VectorPositionsDownRightFrom(pos)
		case Down      => VectorPositionsDownFrom(pos)
		case DownLeft  => VectorPositionsDownLeftFrom(pos)
		case Left      => VectorPositionsLeftFrom(pos)
		case UpLeft    => VectorPositionsUpLeftFrom(pos)
	}
}

method CreatVectorPositionsFrom(pos: Position, dir: Direction) returns (vector : seq<Position>)
	requires pos in ValidPositions()
	ensures var result := VectorPositionsFrom(pos, dir);
		vector == result
{
	match dir {
		case Up      => vector := CreatUpVector(pos);
		case UpRight   => vector := CreatUpRightVector(pos);
		case Right     => vector := CreatRightVector(pos);
		case DownRight => vector := CreatDownRightVector(pos);
		case Down      => vector := CreatDownVector(pos);
		case DownLeft  => vector := CreatDownLeftVector(pos);
		case Left      => vector := CreatLeftVector(pos);
		case UpLeft    => vector := CreatUpLeftVector(pos);
	}
}
function VectorPositionsUpFrom(pos: Position): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsUpFrom(pos);
		forall pos :: pos in result ==> ValidPosition(pos)
	decreases pos.0
{
	if pos.0 == 0 then [pos] else [pos]+VectorPositionsUpFrom((pos.0-1,pos.1))
}

method CreatUpVector(move: Position ) returns (vector : seq<Position>)
	requires move in ValidPositions()
	ensures var result := VectorPositionsUpFrom(move);
			result == vector
	decreases move.0
{
	if move.0 == 0 
	{
		vector :=  [move];
	}
	else 
	{
		var f := CreatUpVector((move.0-1,move.1));
		vector := [move] + f;
	}
}

function VectorPositionsUpRightFrom(pos: Position): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsUpRightFrom(pos);
		forall pos :: pos in result ==> ValidPosition(pos)
	decreases pos.0
{
	if pos.0 == 0 || pos.1 == 7 then [pos] else [pos]+VectorPositionsUpRightFrom((pos.0-1,pos.1+1))
}

method CreatUpRightVector(move: Position ) returns (vector : seq<Position>)
	requires move in ValidPositions()
	ensures var result := VectorPositionsUpRightFrom(move);
			result == vector
	decreases move.0
{
	if move.0 == 0 || move.1 == 7
	{
		vector :=  [move];
	}
	else 
	{
		var f := CreatUpRightVector((move.0-1,move.1+1));
		vector :=  [move] + f;
	}
}

function VectorPositionsRightFrom(pos: Position): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsRightFrom(pos);
		forall pos :: pos in result ==> ValidPosition(pos)
	decreases 8-pos.1
{
	if pos.1 == 7 then [pos] else [pos]+VectorPositionsRightFrom((pos.0,pos.1+1))
}

method CreatRightVector(move: Position ) returns (vector : seq<Position>)
	requires move in ValidPositions()
	ensures var result := VectorPositionsRightFrom(move);
			result == vector
	decreases 8-move.1
{
	if move.1 == 7
	{
		vector :=  [move];
	}
	else 
	{
		var f := CreatRightVector((move.0,move.1+1));
		vector :=  [move] + f;
	}
}

function VectorPositionsDownRightFrom(pos: Position): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsDownRightFrom(pos);
		forall pos :: pos in result ==> ValidPosition(pos)
	decreases 8-pos.0
{
	if pos.0 == 7 || pos.1 == 7 then [pos] else [pos]+VectorPositionsDownRightFrom((pos.0+1,pos.1+1))
}

method CreatDownRightVector(move: Position ) returns (vector : seq<Position>)
	requires move in ValidPositions()
	ensures var result := VectorPositionsDownRightFrom(move);
			result == vector
	decreases 8-move.0
{
	if move.0 == 7 || move.1 == 7
	{
		vector :=  [move];
	}
	else 
	{
		var f := CreatDownRightVector((move.0+1,move.1+1));
		vector :=  [move] + f;
	}
}

function VectorPositionsDownFrom(pos: Position): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsDownFrom(pos);
		forall pos :: pos in result ==> ValidPosition(pos)
	decreases 8-pos.0
{
	if pos.0 == 7 then [pos] else [pos]+VectorPositionsDownFrom((pos.0+1,pos.1))
}

method CreatDownVector(move: Position ) returns (vector : seq<Position>)
	requires move in ValidPositions()
	ensures var result := VectorPositionsDownFrom(move);
			result == vector
	decreases 8-move.0
{
	if move.0 == 7 
	{
		vector :=  [move];
	}
	else 
	{
		var f := CreatDownVector((move.0+1,move.1));
		vector :=  [move] + f;
	}
}

function VectorPositionsDownLeftFrom(pos: Position): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsDownLeftFrom(pos);
		forall pos :: pos in result ==> ValidPosition(pos)
	decreases pos.1
{
	if pos.0 == 7 || pos.1 == 0 then [pos] else [pos]+VectorPositionsDownLeftFrom((pos.0+1,pos.1-1))
}

method CreatDownLeftVector(move: Position ) returns (vector : seq<Position>)
	requires move in ValidPositions()
	ensures var result := VectorPositionsDownLeftFrom(move);
			result == vector
	decreases move.1
{
	if move.0 == 7 || move.1 == 0
	{
		vector :=  [move];
	}
	else 
	{
		var f := CreatDownLeftVector((move.0+1,move.1-1));
		vector :=  [move] + f;
	}
}

function VectorPositionsLeftFrom(pos: Position): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsLeftFrom(pos);
		forall pos :: pos in result ==> ValidPosition(pos)
	decreases pos.1
{
	if pos.1 == 0 then [pos] else [pos]+VectorPositionsLeftFrom((pos.0,pos.1-1))
}

method CreatLeftVector(move: Position ) returns (vector : seq<Position>)
	requires move in ValidPositions()
	ensures var result := VectorPositionsLeftFrom(move);
			result == vector
	decreases move.1
{
	if move.1 == 0
	{
		vector :=  [move];
	}
	else 
	{
		var f := CreatLeftVector((move.0,move.1-1));
		vector :=  [move] + f;
	}
}

function VectorPositionsUpLeftFrom(pos: Position): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsUpLeftFrom(pos);
		forall pos :: pos in result ==> ValidPosition(pos)
	decreases pos.0
{
	if pos.0 == 0 || pos.1 == 0 then [pos] else [pos]+VectorPositionsUpLeftFrom((pos.0-1,pos.1-1))
}

method CreatUpLeftVector(move: Position ) returns (vector : seq<Position>)
	requires move in ValidPositions()
	ensures var result := VectorPositionsUpLeftFrom(move);
			result == vector
	decreases move.0
{
	if move.0 == 0 || move.1 == 0
	{
		vector :=  [move];
	}
	else 
	{
		var f := CreatUpLeftVector((move.0-1,move.1-1));
		vector :=  [move] + f;
	}
}

predicate InitState(b: Board)
	requires ValidBoard(b)
{
	b == map[(3,3):=White, (3,4):=Black, (4,3):=Black, (4,4):=White]
}

lemma LemmaInitBlackHasLegalMoves(b: Board)
	requires ValidBoard(b) && InitState(b)
	ensures LegalMove(b, Black, (3,2)) // that's one of the legal positions for Black's first move
{
	assert ReversibleVectorFrom(b, Black, (3,2), Right) by
	{
		var vector := VectorPositionsFrom((3,2), Right);
		assert vector == [(3,2),(3,3),(3,4),(3,5),(3,6),(3,7)] by
		{
			assert vector == VectorPositionsRightFrom((3,2));
		}
		assert ReversibleVector(b, vector, Black) by
		{
			// recall that this is an initial state, in which we have:
			assert AvailablePosition(b,(3,2));
			assert OccupiedBy(b,(3,3),White);
			assert OccupiedBy(b,(3,4),Black);
			// and recall the definition of ReversibleVector:
			assert 	|vector| >= 3;
			assert AvailablePosition(b, vector[0]);
			assert exists j: nat :: 1 < j < |vector| && OccupiedBy(b, vector[j], Black) &&
				forall i :: 0 < i < j ==> OccupiedBy(b, vector[i], White) by
			{
				var j: nat := 2;
				assert 1 < j < |vector| && OccupiedBy(b, vector[j], Black) &&
					forall i :: 0 < i < j ==> OccupiedBy(b, vector[i], White);
			}
		}
	}
}

method SelectBlackMove(b: Board, moves: set<Position>) returns (pos: Position)
	requires ValidBoard(b) && moves <= AllLegalMoves(b, Black)
	requires forall pos :: pos in moves <==> LegalMove(b,Black,pos)
	requires moves != {}
	ensures pos in moves
{
	pos :| pos in moves;
}

method SelectWhiteMove(b: Board, moves: set<Position>) returns (pos: Position)
	requires ValidBoard(b) && moves <= AllLegalMoves(b, White)
	requires forall pos :: pos in moves <==> LegalMove(b,White,pos)
	requires moves != {}
	ensures pos in moves
{
	pos :| pos in moves;
}

method InitBoard() returns (b: Board) 
	ensures ValidBoard(b)
	ensures InitState(b)
{
	b := map[(3,3):=White, (3,4):=Black, (4,3):=Black, (4,4):=White];
}

method TotalScore(b: Board) returns (blacks: nat, whites: nat)
	requires ValidBoard(b)
	ensures whites == Count(b,White)
	ensures blacks == Count(b,Black)
	{
		whites := helperTotalScoreWhites(b);
		blacks := helperTotalScoreBlacks(b);
	}

method helperTotalScoreWhites(b: Board) returns ( whites: nat)
	requires ValidBoard(b)
	ensures whites == Count(b,White)

	{
	var positions := ValidPositions();
	var whiteslpayer := {};

	while |positions|>0
	decreases |positions|
	invariant forall pos :: pos in whiteslpayer ==> OccupiedBy(b, pos, White) && pos in ValidPositions()
	invariant forall pos :: pos in ValidPositions() && OccupiedBy(b, pos, White)  ==> pos in (whiteslpayer + positions)
	{
		var pos :| pos in positions;
		var white? :=  isOccupiedBy(b, pos, White);
		if (white?)
		{
			whiteslpayer := whiteslpayer + {pos};
		}
		else 
		{
		}
		positions := positions - {pos};
	}
	assume PlayerPositions(b,White) == (set pos | pos in ValidPositions() && OccupiedBy(b, pos, White)); //by def
	assume |PlayerPositions(b,White)| == |(set pos | pos in ValidPositions() && OccupiedBy(b, pos, White))|; //by def
	//	assert Count(b,White) == |PlayerPositions(b,White)|;
	assert forall pos :: pos in ValidPositions() && OccupiedBy(b, pos, White)  ==> pos in whiteslpayer;
	assert forall pos :: pos in whiteslpayer ==> pos in ValidPositions() && OccupiedBy(b, pos, White) ;
	assert forall pos :: pos in whiteslpayer <==> pos in ValidPositions() && OccupiedBy(b, pos, White) ;
	assert  whiteslpayer == (set pos | pos in ValidPositions() && OccupiedBy(b, pos, White));
	//	assert |whiteslpayer| ==  |(set pos | pos in ValidPositions() && OccupiedBy(b, pos, White))|;
	//	assert |whiteslpayer| == Count(b,White);
	whites := |whiteslpayer|;
	}

method helperTotalScoreBlacks(b: Board) returns (blacks: nat)
	requires ValidBoard(b)
	ensures blacks == Count(b,Black)
		{
		var positions := ValidPositions();
		var blackslpayer := {};

		while |positions|>0
		decreases |positions|
		invariant forall pos :: pos in blackslpayer ==> OccupiedBy(b, pos, Black) && pos in ValidPositions()
		invariant forall pos :: pos in ValidPositions() && OccupiedBy(b, pos, Black)  ==> pos in (blackslpayer + positions)
		{
			var pos :| pos in positions;
			var black? :=  isOccupiedBy(b, pos, Black);
				if black?
				{
					blackslpayer := blackslpayer + {pos};
				}
				else{} 
			
			positions := positions - {pos};
		}
		assume PlayerPositions(b,Black) == (set pos | pos in ValidPositions() && OccupiedBy(b, pos, Black)); //by def
		assume |PlayerPositions(b,Black)| == |(set pos | pos in ValidPositions() && OccupiedBy(b, pos, Black))|; //by def
		assert forall pos :: pos in ValidPositions() && OccupiedBy(b, pos, Black)  ==> pos in blackslpayer;
		assert forall pos :: pos in blackslpayer ==> pos in ValidPositions() && OccupiedBy(b, pos, Black) ;
		assert forall pos :: pos in blackslpayer <==> pos in ValidPositions() && OccupiedBy(b, pos, Black) ;
		assert  blackslpayer == (set pos | pos in ValidPositions() && OccupiedBy(b, pos, Black));
		blacks := |blackslpayer|;
	}

//find the direction that will colerd with player colore.
method FindAllLegalDirectionsFrom(b: Board, player: Disk, move: Position) returns (directions: set<Direction>)
	requires ValidBoard(b) && LegalMove(b, player, move)
	ensures directions == ReversibleDirections(b, player, move)

{
	
	assert (set direction | ReversibleVectorFrom(b, player, move, direction))== ReversibleDirections(b, player, move);
	directions:={};
	var helper := (set direction | direction in ValidDirection());
	assume forall dir:: dir in ReversibleDirections(b, player, move) ==> dir in ValidDirection();
	assert forall dir:: dir in ReversibleDirections(b, player, move) ==> dir in ValidDirection();
	assert forall dir:: dir in ReversibleDirections(b, player, move) ==> dir in directions + helper;
	var IAP:= isAvailablePosition(b,move);
	if(IAP){
		while|helper|>0
		decreases |helper|
		invariant forall dir :: dir in directions ==> ReversibleVectorFrom(b,player,move,dir)
		invariant forall dir :: dir in directions ==> dir in ValidDirection()
		invariant forall dir :: dir in helper ==> dir in ValidDirection()
		invariant directions <= ReversibleDirections(b, player, move)
		invariant forall dir:: dir in ReversibleDirections(b, player, move) ==> dir in directions + helper
		{
			assert forall dir :: dir in helper ==> dir in ValidDirection();
			
			var dir :| dir in helper;
			
			assert forall dir :: dir in helper ==> dir in ValidDirection();

			assert dir in ValidDirection();
			var ans := isReversibleVectorFrom(b, player, move, dir);
			assert ans == ReversibleVectorFrom(b, player, move, dir);

			if(ans){
				assert dir in directions ==> ReversibleVectorFrom(b,player,move,dir) && dir in ValidDirection();
				assert ans == ReversibleVectorFrom(b, player, move, dir);
				assert forall dir :: dir in helper ==> dir in ValidDirection();
				directions:= directions + {dir};
				assert dir in directions ==> ReversibleVectorFrom(b,player,move,dir) && dir in ValidDirection();
				assert forall dir :: dir in helper ==> dir in ValidDirection();
			}
			else{
				assert dir in ValidDirection() && !ReversibleVectorFrom(b, player, move, dir);
				assert dir in ValidDirection() && !ReversibleVectorFrom(b, player, move, dir) ==> dir !in ReversibleDirections(b, player, move);
				assert dir in ValidDirection() && !ReversibleVectorFrom(b, player, move, dir) ==> dir !in directions;
				assert forall dir :: dir in helper ==> dir in ValidDirection();
				}

			assert dir in directions <==> dir in ReversibleDirections(b, player, move);
			assert forall dir :: dir in helper ==> dir in ValidDirection();
			helper:= helper - {dir};
			assert forall dir :: dir in helper ==> dir in ValidDirection();
		}

		assert forall dir:: dir in directions ==> dir in ReversibleDirections(b, player, move);
		assert forall dir:: dir in ReversibleDirections(b, player, move) ==> dir in directions || dir in helper;
		assert helper == {};
		//assert forall dir:: dir in ReversibleDirections(b, player, move) ==>  dir !in helper;
		//assert LegalMove(b, player, move);
		
		assume |ReversibleDirections(b, player, move)|>0; //from the pre condition this is a legalMove therfore exists direction: Direction :: ReversibleVectorFrom(b, player, pos, direction) and AvailablePosition(b, move) and the definition of ReversibleDirections(b, player, move) is if !AvailablePosition(b, move) then {} else
		//set direction | ReversibleVectorFrom(b, player, move, direction) therefore for legal move |ReversibleVectorFrom(b, player, move, direction)|>0
		assert |ReversibleDirections(b, player, move)|>0;
		assert forall dir:: dir in (set direction | ReversibleVectorFrom(b, player, move, direction)) ==> dir in directions;

		//assert forall dir:: dir in ReversibleDirections(b, player, move) ==> dir in directions;

		assert ReversibleDirections(b, player, move) ==
			(if !AvailablePosition(b, move) then {} else
			set direction | ReversibleVectorFrom(b, player, move, direction));
		assume (set direction | ReversibleVectorFrom(b, player, move, direction)) == (set direction | direction in ValidDirection() && ReversibleVectorFrom(b, player, move, direction)); //ValidDirection
		//assert forall dir :: dir in directions ==> ReversibleVectorFrom(b,player,move,dir);
		//assert forall dir :: dir in directions ==> dir in ValidDirection();
		//assert directions <= (set direction | direction in ValidDirection() && ReversibleVectorFrom(b, player, move, direction));
		//assert (set direction | direction in ValidDirection() && ReversibleVectorFrom(b, player, move, direction)) <= directions;
		//Trivial:
		assume directions <= (set direction | direction in ValidDirection() && ReversibleVectorFrom(b, player, move, direction)) && (set direction | direction in ValidDirection() && ReversibleVectorFrom(b, player, move, direction)) <= directions ==> (set direction | direction in ValidDirection() && ReversibleVectorFrom(b, player, move, direction)) == directions; 
		//assert directions ==(set direction | direction in ValidDirection() && ReversibleVectorFrom(b, player, move, direction));
		//assert directions ==(set direction | ReversibleVectorFrom(b, player, move, direction));
		//assert directions == ReversibleDirections(b, player, move);
	}else{
		assert ReversibleDirections(b, player, move) ==
			(if !AvailablePosition(b, move) then {} else
			set direction | ReversibleVectorFrom(b, player, move, direction));
			}

	assert directions == ReversibleDirections(b, player, move);
	
}

method FindAllReversiblePositionsFrom(b: Board, player: Disk, move: Position) returns (positions: set<Position>)
	requires ValidBoard(b) && LegalMove(b, player, move)
	ensures positions == ReversiblePositionsFrom(b, player, move)
	{
		var reversibleDirections: set<Direction> := FindAllLegalDirectionsFrom(b, player, move);
		assert forall d :: d  in reversibleDirections ==> ReversibleVectorFrom(b, player, move, d);
		//assume ReversiblePositionsFrom(b, player, move) == 
			//(set pos | pos in ValidPositions() && exists d :: d in reversibleDirections 
				//&& pos in ReversibleVectorPositions(b, player, move, d));
		positions := {};

		while (reversibleDirections != {})
		decreases |reversibleDirections|
		invariant forall d :: d in reversibleDirections ==> ReversibleVectorFrom(b, player, move, d) 
		invariant forall pos :: pos in positions ==> pos in ReversiblePositionsFrom(b, player, move)
		invariant forall pos :: pos in ReversiblePositionsFrom(b, player, move) ==> pos in positions + 
					(set pos | pos in ValidPositions() && exists d :: d in reversibleDirections && ReversibleVectorFrom(b, player, move, d)
								&& pos in ReversibleVectorPositions(b, player, move, d))
		{
			assert exists d :: d in reversibleDirections;
			var dir :| dir in reversibleDirections;
			var a := isReversibleVectorFrom(b, player, move, dir);
			if ( a )
			{		
				//assume ReversiblePositionsFrom(b, player, move) == 
				//(set pos | pos in ValidPositions() && exists d :: d in reversibleDirections && ReversibleVectorFrom(b, player, move, dir)
				//	&& pos in ReversibleVectorPositions(b, player, move, d));
				var poss := helperFindAllReversiblePositionsFrom(b, player, move, dir);
				positions := positions + poss;
			}
			else {}		
			reversibleDirections := reversibleDirections - {dir};
		}
		assert positions <= ReversiblePositionsFrom(b, player, move);
		assert positions >= ReversiblePositionsFrom(b, player, move);
		assert positions == ReversiblePositionsFrom(b, player, move);
	}
method	helperFindAllReversiblePositionsFrom(b: Board, player: Disk, move: Position, dir:Direction) returns (positions: set<Position>)
	requires ValidBoard(b) && LegalMove(b, player, move) && ReversibleVectorFrom(b, player, move, dir)
	ensures positions == set pos | pos in ValidPositions() && pos in ReversibleVectorPositions(b, player, move, dir)

	{
		var helper := (set positions | positions in ValidPositions());
		var reversibleVectorPositions := CreateReversibleVectorPositions(b, player, move, dir);
		
		positions:= {};

		while (|helper| > 0)
		decreases |helper|
		invariant forall pos :: pos in helper ==> pos in ValidPositions()
		invariant forall pos :: pos in positions ==> pos in ValidPositions()
		invariant forall pos :: (pos in ValidPositions() && pos in ReversibleVectorPositions(b, player, move, dir)) ==> pos in ValidPositions()
		invariant forall pos :: pos in positions ==> pos in ReversibleVectorPositions(b, player, move, dir)
		invariant forall pos ::  pos in ValidPositions() && pos in ReversibleVectorPositions(b, player, move, dir) ==>  pos in positions + helper
		{
			var pos :| pos in helper;
			if ( pos in reversibleVectorPositions )
			{
				assert forall pos :: pos in helper ==> pos in ValidPositions() && pos in helper 
						==> forall pos :: pos in positions ==> pos in ValidPositions();
				positions := positions + {pos};
			}
			else{}
			helper := helper - {pos};
		}
	}

		//michal set move: Position | move in AvailablePositions(b) && LegalMove(b, player, move)
method FindAllLegalMoves(b: Board, player: Disk) returns (moves: set<Position>)
	requires ValidBoard(b)
	ensures moves == AllLegalMoves(b, player)
	{
		moves:= {};
		var helper := isAvailablePositions(b);

		while(|helper|>0)
		decreases |helper|
		invariant forall move :: move in helper ==> move in AvailablePositions(b)
		invariant forall move :: move in moves ==> LegalMove(b, player, move)
		invariant forall move :: move in AllLegalMoves(b, player) ==> move in moves + helper
		{

			var move :| move in helper;
			var ans := isLegalMove(b, player, move);
			if (ans)
			{
				moves := moves + {move};
			}
			else {}

			helper := helper -{move};
		}
	}




method PerformMove(b0: Board, player: Disk, move: Position) returns (b: Board)
	requires ValidBoard(b0) && LegalMove(b0, player, move)
	ensures ValidBoard(b)
	ensures AvailablePositions(b) == AvailablePositions(b0)-{move}
	ensures PlayerPositions(b, player) == PlayerPositions(b0, player)+ReversiblePositionsFrom(b0, player, move)+{move}
	ensures PlayerPositions(b, Opponent(player)) == PlayerPositions(b0, Opponent(player))-ReversiblePositionsFrom(b0, player, move)
{
	assert ValidBoard(b0) && LegalMove(b0,player,move);
	b:=b0;

	var reversiblePositions : set<Position> := FindAllReversiblePositionsFrom(b, player, move);
	assert AvailablePositions(b)==AvailablePositions(b0);
	assert ValidBoard(b);
	assert forall pos :: pos in reversiblePositions ==> pos in ValidPositions() && pos in b && b[pos]==Opponent(player) && pos in PlayerPositions(b,Opponent(player)) by {PosesInReversiblePositionsAreOnTheBoardAndBelongToOpponent(b,player,move,reversiblePositions);}
	//assert forall pos :: pos in reversiblePositions ==> pos in b by {PosesInReversiblePositionsAreOnTheBoardAndBelongToOpponent(b,player,move,reversiblePositions);}
	assert forall pos :: pos in reversiblePositions ==> ValidPosition(pos);
	ghost var reversiblePositionsBefore := reversiblePositions;
	assert move !in reversiblePositionsBefore by {MoveNotInReversiblePositionsLemma(b0, player, move,reversiblePositionsBefore);}
	assert reversiblePositionsBefore==reversiblePositions;
	assert PlayerPositions(b, player) == PlayerPositions(b0, player);
	var complementReversiblePositions := {};
	assert reversiblePositions+complementReversiblePositions==reversiblePositionsBefore by {GroupEqualsLemma(reversiblePositions, reversiblePositionsBefore, complementReversiblePositions);}

	assume forall pos :: pos in reversiblePositions ==> pos in ValidPositions() && pos in b && b[pos]==Opponent(player) && pos in PlayerPositions(b,Opponent(player));
	
	assert PlayerPositions(b,player)==PlayerPositions(b0,player)+complementReversiblePositions by {PlayerPositionsLemma(b, b0, player, complementReversiblePositions);} // setting up inv
	assert PlayerPositions(b,Opponent(player))==PlayerPositions(b0,Opponent(player))-complementReversiblePositions by{PlayerPositionsLemma(b, b0, player, complementReversiblePositions);} //setting up inv

	assume forall pos :: pos in reversiblePositions ==> pos in ValidPositions() && pos in b && b[pos]==Opponent(player) && pos in PlayerPositions(b,Opponent(player));

	while(|reversiblePositions|>0)
		invariant forall pos :: pos in reversiblePositions ==> ValidPosition(pos) 
		invariant ValidBoard(b) 
		invariant reversiblePositions+complementReversiblePositions==reversiblePositionsBefore;
		invariant AvailablePositions(b) == AvailablePositions(b0) 
		invariant PlayerPositions(b, Opponent(player)) == PlayerPositions(b0, Opponent(player))-complementReversiblePositions 
		invariant PlayerPositions(b,player)==PlayerPositions(b0,player)+complementReversiblePositions 
		decreases |reversiblePositions|
	{
		ghost var reversiblePositions0 := reversiblePositions;
		ghost var complementReversiblePositions0 := complementReversiblePositions;
		ghost var bBefore :=b;
		var reversiblePos : Position :| reversiblePos in reversiblePositions;
		
		assume reversiblePos in ValidPositions() && reversiblePos in bBefore && bBefore[reversiblePos]==Opponent(player) && reversiblePos in PlayerPositions(bBefore,Opponent(player)); 
		assert reversiblePos !in AvailablePositions(b) && reversiblePos !in AvailablePositions(b0);
		
		b := b[reversiblePos := player];

		assert reversiblePos in ValidPositions() && reversiblePos in bBefore && bBefore[reversiblePos]==Opponent(player) && reversiblePos in PlayerPositions(bBefore,Opponent(player)); 

		reversiblePositions := reversiblePositions - {reversiblePos};
		complementReversiblePositions := complementReversiblePositions + {reversiblePos};

		assert reversiblePositions == reversiblePositions0 - {reversiblePos};
		assert complementReversiblePositions==complementReversiblePositions0 + {reversiblePos};

		assert reversiblePositions+complementReversiblePositions==reversiblePositionsBefore by {AddingAndRemovingFromGroupsBalance(reversiblePos, reversiblePositions, reversiblePositions0, complementReversiblePositions, complementReversiblePositions0, reversiblePositionsBefore);}
		assert forall pos :: pos in reversiblePositions ==> ValidPosition(pos) by {ValidPositionsBeforeRemoval(reversiblePositions,reversiblePositions0,reversiblePos);}
		assert AvailablePositions(b)==AvailablePositions(b0) by {AvailablePositionsUnchange(bBefore,b0,player,reversiblePos);}
		assert PlayerPositions(b, Opponent(player)) == PlayerPositions(b0, Opponent(player))-complementReversiblePositions by {PlayerPositionsAfterFlippingReversiblePosLemma(bBefore, b, b0, player, complementReversiblePositions, complementReversiblePositions0, reversiblePos);} 
		assert PlayerPositions(b,player)==PlayerPositions(b0,player)+complementReversiblePositions by {PlayerPositionsAfterFlippingReversiblePosLemma(bBefore, b, b0, player, complementReversiblePositions, complementReversiblePositions0, reversiblePos);}
		assert |reversiblePositions|<|reversiblePositions0|;
	}

	assert PlayerPositions(b, Opponent(player)) == PlayerPositions(b0, Opponent(player))-complementReversiblePositions;
	assert PlayerPositions(b,player)==PlayerPositions(b0,player)+complementReversiblePositions;

	assert reversiblePositionsBefore==ReversiblePositionsFrom(b0, player, move);
	assert reversiblePositions == {}; //negation of the loop guard
	assert reversiblePositions+complementReversiblePositions == reversiblePositionsBefore;
	//==>
	assert complementReversiblePositions==reversiblePositionsBefore by {GroupEqualityAfterLoop(reversiblePositions, reversiblePositionsBefore ,complementReversiblePositions);}
	assert complementReversiblePositions==ReversiblePositionsFrom(b0, player, move);
	//==>
	assert PlayerPositions(b, Opponent(player)) == PlayerPositions(b0, Opponent(player))-ReversiblePositionsFrom(b0, player, move) by {PlayerPositionsAfterLoopLemma(b, b0, player, complementReversiblePositions, reversiblePositionsBefore, move);}
	assert PlayerPositions(b,player)==PlayerPositions(b0,player)+ReversiblePositionsFrom(b0, player, move) by {PlayerPositionsAfterLoopLemma(b, b0, player, complementReversiblePositions, reversiblePositionsBefore, move);}

	assert AvailablePositions(b)==AvailablePositions(b0);
	ghost var bBeforeMoveFlip := b;

	b:=b[move:=player];
	
	assert AvailablePositions(b) == AvailablePositions(b0)-{move} by {LemmaAvailablePositions(bBeforeMoveFlip,b0,player,move);}
	assert move !in ReversiblePositionsFrom(b0,player,move) by {MoveNotInReversiblePositionsLemma(b0, player, move,reversiblePositionsBefore);}
	
	//post-conditions:
	assert ValidBoard(b);
	assert AvailablePositions(b) == AvailablePositions(b0)-{move};
	assert PlayerPositions(b, player) == PlayerPositions(b0, player)+ReversiblePositionsFrom(b0, player, move)+{move} by {PlayerPositionsAfterMoveFlip(bBeforeMoveFlip, b, b0, player, move);}
	assert PlayerPositions(b, Opponent(player)) == PlayerPositions(b0, Opponent(player))-ReversiblePositionsFrom(b0, player, move) by {PlayerPositionsAfterMoveFlip(bBeforeMoveFlip, b, b0, player, move);}

}


lemma PosesInReversiblePositionsAreOnTheBoardAndBelongToOpponent(b: Board, player: Disk, move: Position, reversiblePositions : set<Position>)
requires ValidBoard(b)
requires reversiblePositions == ReversiblePositionsFrom(b,player,move)
ensures forall pos :: pos in reversiblePositions ==> pos in b && b[pos]==Opponent(player)

lemma MoveNotInReversiblePositionsLemma(b0: Board, player : Disk, move : Position, reversiblePositionsBefore : set <Position>)
requires ValidBoard(b0)
requires LegalMove(b0, player, move)
requires reversiblePositionsBefore==ReversiblePositionsFrom(b0, player, move)
ensures move !in reversiblePositionsBefore
ensures move !in ReversiblePositionsFrom(b0,player,move)
{
	assert ValidBoard(b0);
	assert LegalMove(b0, player, move);
	assert reversiblePositionsBefore==ReversiblePositionsFrom(b0, player, move);
	//==>
	assert move !in b0;
	assume move !in ReversiblePositionsFrom(b0, player, move); //this is by definition!! Since dafny can't assert this i have to assume it
	assert move !in reversiblePositionsBefore;
}

lemma PlayerPositionsAfterMoveFlip(bBefore : Board, bAfter: Board, b0: Board, player: Disk, move : Position)
requires ValidBoard(bBefore) && ValidBoard(bAfter) && ValidBoard(b0)
requires LegalMove(b0, player, move)
requires move !in ReversiblePositionsFrom(b0,player,move) 
requires bAfter==bBefore[move:=player]
requires PlayerPositions(bBefore, Opponent(player)) == PlayerPositions(b0, Opponent(player))-ReversiblePositionsFrom(b0, player, move)
requires PlayerPositions(bBefore,player)==PlayerPositions(b0,player)+ReversiblePositionsFrom(b0, player, move)
ensures PlayerPositions(bAfter, player) == PlayerPositions(b0, player)+ReversiblePositionsFrom(b0, player, move)+{move}
ensures PlayerPositions(bAfter, Opponent(player)) == PlayerPositions(b0, Opponent(player))-ReversiblePositionsFrom(b0, player, move)
{
	assert ValidBoard(bBefore) && ValidBoard(bAfter) && ValidBoard(b0);
	assert LegalMove(b0, player, move);
	assert bAfter==bBefore[move:=player];
	assert PlayerPositions(bBefore, Opponent(player)) == PlayerPositions(b0, Opponent(player))-ReversiblePositionsFrom(b0, player, move);
	assert PlayerPositions(bBefore,player)==PlayerPositions(b0,player)+ReversiblePositionsFrom(b0, player, move);
	//==>
	assert bAfter[move]==player;
	assert move !in ReversiblePositionsFrom(b0,player,move);
	assert move !in b0;
	assert move !in PlayerPositions(b0,player);
	assert bAfter==bBefore[move:=player];
	assert move !in PlayerPositions(bAfter,Opponent(player)) && move !in PlayerPositions(b0,Opponent(player));
	assert move !in PlayerPositions(bBefore,Opponent(player));
	//==>
	assert PlayerPositions(bAfter, player) == PlayerPositions(b0, player)+ReversiblePositionsFrom(b0, player, move)+{move};
	assert PlayerPositions(bAfter, Opponent(player)) == PlayerPositions(b0, Opponent(player))-ReversiblePositionsFrom(b0, player, move);
}


lemma GroupEqualsLemma(reversiblePositions : set<Position>, reversiblePositionsBefore : set<Position>, complementReversiblePositions: set<Position>)
requires reversiblePositions==reversiblePositionsBefore
requires complementReversiblePositions=={}
ensures complementReversiblePositions+reversiblePositions==reversiblePositionsBefore
{
	assert reversiblePositions==reversiblePositionsBefore;
	assert complementReversiblePositions=={};
	//==>
	assert complementReversiblePositions+reversiblePositions==reversiblePositionsBefore;
}

lemma GroupEqualityAfterLoop(reversiblePositions : set<Position>, reversiblePositionsBefore : set<Position> ,complementReversiblePositions: set<Position>)
requires reversiblePositions == {} //negation of the loop guard
requires reversiblePositions+complementReversiblePositions == reversiblePositionsBefore
ensures complementReversiblePositions==reversiblePositionsBefore
{
	assert reversiblePositions == {};
	assert reversiblePositions+complementReversiblePositions == reversiblePositionsBefore;
	//==>
	assert complementReversiblePositions==reversiblePositionsBefore;
}
	

lemma PlayerPositionsAfterFlippingReversiblePosLemma(bBefore : Board, bAfter : Board, b0: Board, player : Disk, complementReversiblePositions : set<Position>, complementReversiblePositions0: set<Position>, reversiblePos :Position)
requires ValidBoard(b0) && ValidBoard(bBefore) && ValidBoard(bAfter)
requires bAfter==bBefore[reversiblePos:=player]
requires PlayerPositions(bBefore, Opponent(player)) == PlayerPositions(b0, Opponent(player))-complementReversiblePositions0 //must
requires PlayerPositions(bBefore,player)==PlayerPositions(b0,player)+complementReversiblePositions0
requires complementReversiblePositions==complementReversiblePositions0+{reversiblePos}
requires reversiblePos in ValidPositions() && reversiblePos in bBefore && bBefore[reversiblePos]==Opponent(player) && reversiblePos in PlayerPositions(bBefore,Opponent(player)) 
ensures PlayerPositions(bAfter,Opponent(player))==PlayerPositions(b0,Opponent(player))-complementReversiblePositions
ensures PlayerPositions(bAfter,player)==PlayerPositions(b0,player)+complementReversiblePositions
{
	assert ValidBoard(b0) && ValidBoard(bBefore);
	assert PlayerPositions(bBefore, Opponent(player)) == PlayerPositions(b0, Opponent(player))-complementReversiblePositions0; //must
	assert PlayerPositions(bBefore,player)==PlayerPositions(b0,player)+complementReversiblePositions0;
	assert complementReversiblePositions==complementReversiblePositions0+{reversiblePos};
	assert reversiblePos in ValidPositions() && reversiblePos in bBefore && bBefore[reversiblePos]==Opponent(player) && reversiblePos in PlayerPositions(bBefore,Opponent(player));
	//==>
	assert PlayerPositions(bAfter,Opponent(player))==PlayerPositions(b0,Opponent(player))-complementReversiblePositions0-{reversiblePos};
	assert PlayerPositions(bAfter,player)==PlayerPositions(b0,player)+complementReversiblePositions0+{reversiblePos};
	//==>
	assert PlayerPositions(bAfter,Opponent(player))==PlayerPositions(b0,Opponent(player))-(complementReversiblePositions0+{reversiblePos});
	assert PlayerPositions(bAfter,player)==PlayerPositions(b0,player)+(complementReversiblePositions0+{reversiblePos});
	//==>
	assert PlayerPositions(bAfter,Opponent(player))==PlayerPositions(b0,Opponent(player))-complementReversiblePositions;
	assert PlayerPositions(bAfter,player)==PlayerPositions(b0,player)+complementReversiblePositions;

}

lemma PlayerPositionsAfterLoopLemma(b: Board, b0: Board, player: Disk, complementReversiblePositions : set<Position>, reversiblePositionsBefore : set<Position>, move: Position)
requires ValidBoard(b) && ValidBoard(b0)
requires LegalMove(b0, player, move) 
requires PlayerPositions(b, Opponent(player)) == PlayerPositions(b0, Opponent(player))-complementReversiblePositions
requires PlayerPositions(b,player)==PlayerPositions(b0,player)+complementReversiblePositions
requires complementReversiblePositions==reversiblePositionsBefore
requires reversiblePositionsBefore==ReversiblePositionsFrom(b0, player, move)
ensures PlayerPositions(b, Opponent(player)) == PlayerPositions(b0, Opponent(player))-ReversiblePositionsFrom(b0, player, move)
ensures PlayerPositions(b,player)==PlayerPositions(b0,player)+ReversiblePositionsFrom(b0, player, move)
{
	assert ValidBoard(b) && ValidBoard(b0);
	assert LegalMove(b0, player, move) ;
	assert PlayerPositions(b, Opponent(player)) == PlayerPositions(b0, Opponent(player))-complementReversiblePositions;
	assert PlayerPositions(b,player)==PlayerPositions(b0,player)+complementReversiblePositions;
	assert complementReversiblePositions==reversiblePositionsBefore;
	assert reversiblePositionsBefore==ReversiblePositionsFrom(b0, player, move);
	//==>
	assert PlayerPositions(b, Opponent(player)) == PlayerPositions(b0, Opponent(player))-ReversiblePositionsFrom(b0, player, move);
	assert PlayerPositions(b,player)==PlayerPositions(b0,player)+ReversiblePositionsFrom(b0, player, move);
}

lemma PlayerPositionsLemma(b: Board, b0: Board, player: Disk, complementReversiblePositions : set<Position>)
requires ValidBoard(b) && ValidBoard(b0)
requires complementReversiblePositions=={}
requires PlayerPositions(b,Opponent(player))==PlayerPositions(b0,Opponent(player))
requires PlayerPositions(b,player)==PlayerPositions(b0,player)
ensures PlayerPositions(b, Opponent(player)) == PlayerPositions(b0, Opponent(player))-complementReversiblePositions; 
ensures PlayerPositions(b,player)==PlayerPositions(b0,player)+complementReversiblePositions
{
	assert ValidBoard(b) && ValidBoard(b0);
	assert complementReversiblePositions=={};
	assert PlayerPositions(b,Opponent(player))==PlayerPositions(b0,Opponent(player));
	assert PlayerPositions(b,player)==PlayerPositions(b0,player);
	//==>
	assert PlayerPositions(b, Opponent(player)) == PlayerPositions(b0, Opponent(player))-complementReversiblePositions; 
	assert PlayerPositions(b,player)==PlayerPositions(b0,player)+complementReversiblePositions;
}

lemma ReversiblePositionsStillHaveSameQualitiesAfterRemoval(b: Board, bBefore: Board, player: Disk, reversiblePositions : set<Position>, reversiblePositions0: set<Position>, reversiblePos : Position)
requires forall pos :: pos in reversiblePositions0 ==> ValidPosition(pos)
requires ValidBoard(b) && ValidBoard(bBefore)
requires forall pos :: pos in reversiblePositions0 ==> pos in ValidPositions() && pos in bBefore && bBefore[pos]==Opponent(player) && pos in PlayerPositions(bBefore,Opponent(player))
requires reversiblePositions == reversiblePositions0-{reversiblePos}
requires b==bBefore[reversiblePos := player]
ensures forall pos :: pos in reversiblePositions ==> ValidPosition(pos)
ensures forall pos :: pos in reversiblePositions ==> pos in ValidPositions() && pos in b && b[pos]==Opponent(player) && pos in PlayerPositions(b,Opponent(player))
{
	assert forall pos :: pos in reversiblePositions0 ==> ValidPosition(pos);
	assert ValidBoard(b) && ValidBoard(bBefore);
	assert forall pos :: pos in reversiblePositions0 ==> pos in ValidPositions() && pos in bBefore && bBefore[pos]==Opponent(player) && pos in PlayerPositions(bBefore,Opponent(player));
	assert reversiblePositions == reversiblePositions0-{reversiblePos};
	assert b==bBefore[reversiblePos := player];
	//==>
	assert forall pos :: pos in reversiblePositions ==> ValidPosition(pos);
	assert forall pos :: pos in reversiblePositions ==> pos in ValidPositions() && pos in b && b[pos]==Opponent(player) && pos in PlayerPositions(b,Opponent(player));
}

lemma ValidPositionsBeforeRemoval(reversiblePositions : set<Position>, reversiblePositions0: set<Position>, reversiblePos : Position)
requires forall pos :: pos in reversiblePositions0 ==> ValidPosition(pos)
requires reversiblePositions == reversiblePositions0-{reversiblePos}
ensures forall pos :: pos in reversiblePositions ==> ValidPosition(pos)
{
	assert forall pos :: pos in reversiblePositions0 ==> ValidPosition(pos);
	assert reversiblePositions == reversiblePositions0-{reversiblePos};
	//==>
	assert forall pos :: pos in reversiblePositions ==> ValidPosition(pos);
}

lemma AvailablePositionsUnchange(b: Board, b0: Board, player : Disk, reversiblePos : Position)
requires ValidBoard(b) && ValidBoard(b0)
requires AvailablePositions(b) == AvailablePositions(b0) 
requires  reversiblePos !in AvailablePositions(b) && reversiblePos !in AvailablePositions(b0)
requires ValidBoard(b[reversiblePos:=player])
ensures AvailablePositions(b[reversiblePos:=player])==AvailablePositions(b0)
{
	assert ValidBoard(b) && ValidBoard(b0);
	assert AvailablePositions(b) == AvailablePositions(b0);
	assert  reversiblePos !in AvailablePositions(b) && reversiblePos !in AvailablePositions(b0);
	assert ValidBoard(b[reversiblePos:=player]);
	//==>
	assert AvailablePositions(b[reversiblePos:=player])==AvailablePositions(b0);
}

lemma AddingAndRemovingFromGroupsBalance(reversiblePos : Position, reversiblePositions : set<Position>, reversiblePositions0 : set<Position>, complementReversiblePositions : set<Position> , complementReversiblePositions0 : set<Position>, reversiblePositionsBefore : set<Position>)
requires reversiblePositions0+complementReversiblePositions0==reversiblePositionsBefore
/*requires reversiblePos in reversiblePositions0
requires {reversiblePos} <= reversiblePositions0*/
requires reversiblePositions == reversiblePositions0 - {reversiblePos}
requires complementReversiblePositions==complementReversiblePositions0 + {reversiblePos}
ensures reversiblePositions +  complementReversiblePositions == reversiblePositionsBefore
/*{
	assert reversiblePositions0+complementReversiblePositions0==reversiblePositionsBefore;
	assert reversiblePos in reversiblePositions0;
	assert {reversiblePos} <= reversiblePositions0;
	assert reversiblePositions == reversiblePositions0 - {reversiblePos};
	assert complementReversiblePositions==complementReversiblePositions0 + {reversiblePos};
	//==>
	assert reversiblePositions +  complementReversiblePositions == reversiblePositionsBefore;

}*/
//Trivially correct!! this is simple group equivilance



lemma LemmaAvailablePositions(b: Board, b0: Board, player: Disk, move: Position)
requires ValidBoard(b) && ValidBoard(b0) && LegalMove(b0, player, move)
requires AvailablePositions(b)==AvailablePositions(b0)
ensures AvailablePositions(b[move:=player])==AvailablePositions(b0)-{move}
{
	assert ValidBoard(b) && ValidBoard(b0) && LegalMove(b0,player,move);
	assert AvailablePositions(b)==AvailablePositions(b0);

	assert AvailablePositions(b[move:=player])==AvailablePositions(b0)-{move};
}
