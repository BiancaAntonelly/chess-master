package boardgame;

public class Position {

    //@ spec_public
    private int row;

    //@ spec_public
    private int col;

    /*@ public normal_behavior
      @   ensures this.row == row;
      @   ensures this.col == col;
      @   assignable \this.row, \this.col;
      @*/
    public Position(int row, int col) {
        this.row = row;
        this.col = col;
    }

    /*@ public normal_behavior
      @   ensures \result == row;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ int getRow() {
        return row;
    }

    /*@ public normal_behavior
      @   ensures this.row == row;
      @   assignable \this.row;
      @*/
    public void setRow(int row) {
        this.row = row;
    }

    /*@ public normal_behavior
      @   ensures \result == col;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ int getCol() {
        return col;
    }

    /*@ public normal_behavior
      @   ensures this.col == col;
      @   assignable \this.col;
      @*/
    public void setCol(int col) {
        this.col = col;
    }

    /*@ public normal_behavior
      @   ensures this.row == row;
      @   ensures this.col == col;
      @   assignable \this.row, \this.col;
      @*/
    public void setValues(int row, int col) {
        this.row = row;
        this.col = col;
    }

    /*@ public normal_behavior
      @   ensures \result != null;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ String getString() {
        return row + ", " + col;
    }
}
