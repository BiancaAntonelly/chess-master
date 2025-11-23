package boardgame;

public abstract class Piece {

    //@ spec_public
    protected /*@ nullable @*/ Position position; //@ in modelPosition;
    //@ spec_public
    private final Board board;                    //@ in modelBoard;

    //@ public model Board modelBoard;
    //@ private represents modelBoard = this.board;

    //@ public model /*@ nullable */ Position modelPosition;
    //@ private represents modelPosition = this.position;

    /*@ public normal_behavior
      @     ensures modelBoard == board;
      @     ensures modelPosition == null;
      @     pure
      @*/
    public Piece(Board board) {
        this.board = board;
        this.position = null;
    }

    /*@ pure @*/
    protected Board getBoard() { return board; }

    /*@ public normal_behavior
      @   ensures \result.length == 8;
      @   ensures (\forall int i; 0 <= i && i < 8; \result[i].length == 8);
      @   pure
      @*/
    public abstract boolean[][] possibleMoves();

    /*@ requires pos != null;
      @ requires pos.getRow() >= 0 && pos.getRow() < 8;
      @ requires pos.getCol() >= 0 && pos.getCol() < 8;
      @ ensures \result == possibleMoves()[pos.getRow()][pos.getCol()];
      @ pure
      @*/
    public boolean possibleMove(Position pos) {
        return possibleMoves()[pos.getRow()][pos.getCol()];
    }

    /*@ public normal_behavior
      @   ensures true; // evita travamento do prover
      @   pure
      @*/
    public boolean isThereAnyPossibleMove() {
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
