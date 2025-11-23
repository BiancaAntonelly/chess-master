package boardgame;

public abstract class Piece {

    //@ spec_public
    protected /*@ nullable @*/ Position position; //@ in modelPosition;
    //@ spec_public
    private final Board board;                    //@ in modelBoard;

    //@ public model Board modelBoard;
    //@ private represents modelBoard = board;

    //@ public model /*@ nullable */ Position modelPosition;
    //@ private represents modelPosition = position;

    //@ public invariant modelBoard != null;
    //@ public invariant modelPosition == null
    //@        || (modelPosition.getRow() >= 0 && modelPosition.getRow() < 8
    //@            && modelPosition.getCol() >= 0 && modelPosition.getCol() < 8);

    /*@ public normal_behavior
      @   requires board != null;
      @   ensures modelBoard == board;
      @   ensures modelPosition == null;
      @*/
    public Piece(Board board) {
        this.board = board;
        this.position = null;
    }

    /*@ pure @*/
    protected Board getBoard() { return board; }

    /*@ public normal_behavior
      @   ensures \result != null;
      @   ensures \result.length == 8;
      @   ensures (\forall int i; 0 <= i && i < 8; \result[i].length == 8);
      @*/
    /*@ pure @*/ public abstract boolean[][] possibleMoves();

    /*@ public normal_behavior
      @   requires pos != null;
      @   requires pos.getRow() >= 0 && pos.getRow() < 8;
      @   requires pos.getCol() >= 0 && pos.getCol() < 8;
      @   ensures \result == possibleMoves()[pos.getRow()][pos.getCol()];
      @*/
    /*@ pure @*/ public boolean possibleMove(Position pos) {
        return possibleMoves()[pos.getRow()][pos.getCol()];
    }

    /*@ public normal_behavior
      @   ensures \result <==>
      @     (\exists int i; 0 <= i && i < 8;
      @       (\exists int j; 0 <= j && j < 8;
      @         possibleMoves()[i][j]));
      @*/
    /*@ pure @*/ public boolean isThereAnyPossibleMove() {
        boolean[][] mat = possibleMoves();
        for (boolean[] booleans : mat) {
            for (int j = 0; j < mat.length; j++) {
                if (booleans[j]) {
                    return true;
                }
            }
        }
        return false;
    }
}
