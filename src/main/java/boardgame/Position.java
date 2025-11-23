package boardgame;

public class Position {
    //@ spec_public
    private int row;
    //@ spec_public
    private int col;

    /*@ public normal_behavior
      @     ensures this.row == row;
      @     ensures this.col == col;
      @ pure
      @*/
    public Position(int row, int col) {
        this.row = row;
        this.col = col;
    }

    /*@ public normal_behavior
      @ ensures \result == this.row;
      @ pure
      @*/
    public int getRow() {
        return row;
    }

    /*@ public normal_behavior
      @   requires 0 <= row && row < 8;
      @   ensures this.row == row;
      @*/
    public void setRow(int row) {
        this.row = row;
    }

    /*@ public normal_behavior
      @   ensures \result == col;
      @   pure
      @*/
    public int getCol() {
        return col;
    }

    /*@ public normal_behavior
      @     ensures this.col == col;
      @     assignable this.col;
      @*/
    public void setCol(int col) {
        this.col = col;
    }

    /*@ public normal_behavior
      @     ensures this.row == row;
      @     ensures this.col == col;
      @     assignable this.col, this.row;
      @*/
    public void setValues(int row, int col) {
        this.row = row;
        this.col = col;
    }

    /*@ public normal_behavior
      @   ensures \result != null;
      @   pure
      @*/
    public String getString() {
        return row + ", " + col;
    }

}
