package boardgame;

public abstract class Piece {

    //@ spec_public
    protected /*@ nullable @*/ Position position; //@ in modelPosition;
    //@ spec_public
    private final Board board;
    //@ in modelBoard;

    //@ public model Board modelBoard;
    //@ private represents modelBoard = board;

    //@ public model /*@ nullable */ Position modelPosition;
    //@ private represents modelPosition = position;

    //@ public invariant modelBoard != null;

    /*@ public normal_behavior
      @   requires board != null;
      @   ensures modelBoard == board;
      @   ensures modelPosition == null;
      @   ensures getBoard() == board;
      @*/
    public Piece(Board board) {
        this.board = board;
        this.position = null;
    }

    /*@ public normal_behavior
      @   ensures \result == board;
      @   ensures \result != null;
      @   assignable \nothing;
      @*/
    public /*@ pure non_null @*/ Board getBoard() { return board; }

    public abstract boolean[][] possibleMoves();

    /*@ public normal_behavior
      @   requires pos != null;
      @   requires pos.getRow() >= 0 && pos.getRow() < 8;
      @   requires pos.getCol() >= 0 && pos.getCol() < 8;
      @   requires possibleMoves() != null;
      @   requires possibleMoves().length == 8;
      @   requires possibleMoves()[pos.getRow()] != null;
      @   requires possibleMoves()[pos.getRow()].length == 8;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ boolean possibleMove(Position pos) {
        return possibleMoves()[pos.getRow()][pos.getCol()];
    }

    /*@ public normal_behavior
      @   requires possibleMoves() != null;
      @   requires possibleMoves().length == 8;
      @   requires (\forall int i; 0 <= i && i < 8; possibleMoves()[i] != null && possibleMoves()[i].length == 8);
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ boolean isThereAnyPossibleMove() {
        boolean[][] mat = possibleMoves();
        /*@ loop_invariant 0 <= i && i <= 8;
          @ decreases 8 - i;
          @*/
        for (int i = 0; i < 8; i++) {
            boolean[] booleans = mat[i];
            /*@ loop_invariant 0 <= j && j <= 8;
              @ decreases 8 - j;
              @*/
            for (int j = 0; j < 8; j++) {
                if (booleans[j]) {
                    return true;
                }
            }
        }
        return false;
    }

    /*@ pure @*/
    public /*@ nullable @*/ Position getPosition() {
        return position;
    }
}
