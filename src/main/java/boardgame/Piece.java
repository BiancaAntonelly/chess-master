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
    public Board getBoard() { return board; }

    /*@ public normal_behavior
      @   ensures \result != null;
      @   ensures \result.length == 8;
      @   ensures (\forall int i; 0 <= i && i < 8;
      @               \result[i] != null && \result[i].length == 8);
      @   assignable \nothing;
      @*/
    public abstract boolean[][] possibleMoves();

    /*@ public normal_behavior
      @   requires pos != null;
      @   requires pos.getRow() >= 0 && pos.getRow() < 8;
      @   requires pos.getCol() >= 0 && pos.getCol() < 8;
      @   requires possibleMoves() != null;
      @   requires possibleMoves().length > pos.getRow();
      @   requires possibleMoves()[pos.getRow()] != null;
      @   requires possibleMoves()[pos.getRow()].length > pos.getCol();
      @   ensures \result == possibleMoves()[pos.getRow()][pos.getCol()];
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ boolean possibleMove(Position pos) {
        return possibleMoves()[pos.getRow()][pos.getCol()];
    }

    /*@ public normal_behavior
      @   requires possibleMoves() != null;
      @   requires possibleMoves().length == 8;
      @   requires (\forall int i; 0 <= i && i < 8; possibleMoves()[i] != null && possibleMoves()[i].length == 8);
      @   ensures \result == true ==> (\exists int i, j; 0 <= i && i < 8 && 0 <= j && j < 8; possibleMoves()[i][j]);
      @   ensures \result == false ==> (\forall int i, j; 0 <= i && i < 8 && 0 <= j && j < 8; !possibleMoves()[i][j]);
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ boolean isThereAnyPossibleMove() {
        boolean[][] mat = possibleMoves();

        /*@ loop_invariant mat != null;
          @ loop_invariant 0 <= i && i <= mat.length;
          @ loop_invariant (\forall int k, l; 0 <= k && k < i && 0 <= l && l < mat[k].length; !mat[k][l]);
          @ decreases mat.length - i;
          @*/
        for (int i = 0; i < mat.length; i++) {

            boolean[] booleans = mat[i];

            /*@ loop_invariant booleans != null;
              @ loop_invariant 0 <= j && j <= booleans.length;
              @ loop_invariant (\forall int l; 0 <= l && l < j; !booleans[l]);
              @ decreases booleans.length - j;
              @*/
            for (int j = 0; j < booleans.length; j++) {
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
