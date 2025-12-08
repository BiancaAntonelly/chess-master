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
      @   ensures (\forall int i; 0 <= i && i < 8;
      @               \result[i] != null && \result[i].length == 8);
      @
      @   // Permite criação de arrays e objetos
      @   assignable \everything;
      @*/
    public abstract boolean[][] possibleMoves();

    /*@ public normal_behavior
      @   requires pos != null;
      @   requires pos.getRow() >= 0 && pos.getRow() < 8;
      @   requires pos.getCol() >= 0 && pos.getCol() < 8;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ boolean possibleMove(Position pos) {
        return possibleMoves()[pos.getRow()][pos.getCol()];
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ boolean isThereAnyPossibleMove() {
        boolean[][] mat = possibleMoves();
        for (boolean[] booleans : mat) {
            /*@ loop_invariant 0 <= j && j <= mat.length;
              @*/
            for (int j = 0; j < mat.length; j++) {
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
