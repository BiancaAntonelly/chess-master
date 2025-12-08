package boardgame;

public class Position {

    //@ spec_public
    private int r;

    //@ spec_public
    private int c;

    /*@ public normal_behavior
      @   ensures this.r == row;
      @   ensures this.c == col;
      @*/
    public Position(int row, int col) {
        this.r = row;
        this.c = col;
    }

    /*@ public normal_behavior
      @   ensures \result == r;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ int getRow() {
        return r;
    }

    /*@ public normal_behavior
      @   ensures this.r == row;
      @   assignable r;
      @*/
    public void setRow(int row) {
        this.r = row;
    }

    /*@ public normal_behavior
      @   ensures \result == c;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ int getCol() {
        return c;
    }

    /*@ public normal_behavior
      @   ensures this.c == col;
      @   assignable c;
      @*/
    public void setCol(int col) {
        this.c = col;
    }

    /*@ public normal_behavior
      @   ensures this.r == row;
      @   ensures this.c == col;
      @   assignable r, c;
      @*/
    public void setValues(int row, int col) {
        this.r = row;
        this.c = col;
    }

    /*@ public normal_behavior
      @   ensures \result != null;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ String getString() {
        return r + ", " + c;
    }
}
