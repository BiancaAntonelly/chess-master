package boardgame;

public class Board {
    //@ spec_public
    private final int rows;
    //@ spec_public
    private final int cols;
    //@ spec_public
    private final /*@ nullable @*/ Piece[][] pieces;

    //@ public invariant rows >= 1 && cols >= 1;
    //@ public invariant pieces != null && pieces.length == rows;
    //@ public invariant (\forall int i; 0 <= i && i < rows;
    //@                       pieces[i] != null && pieces[i].length == cols);
    //@ public invariant \typeof(pieces) == \type(Piece[][]);

    /*@ public normal_behavior
      @   requires rows >= 1 && cols >= 1;
      @   ensures this.rows == rows;
      @   ensures this.cols == cols;
      @   ensures pieces != null && pieces.length == rows;
      @   ensures (\forall int i; 0 <= i && i < rows;
      @                pieces[i] != null && pieces[i].length == cols);
      @*/
    public Board(int rows, int cols) {
        if (rows < 1 || cols < 1) {
            throw new BoardException("O tabuleiro precisa de ao menos 1 linha e 1 coluna.");
        }

        this.rows = rows;
        this.cols = cols;
        pieces = new Piece[rows][cols];
    }

    /*@ public normal_behavior
      @   ensures \result == rows;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ int getRows() {
        return rows;
    }

    /*@ public normal_behavior
      @   ensures \result == cols;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ int getCols() {
        return cols;
    }

    /*@ public normal_behavior
      @   requires 0 <= row && row < rows;
      @   requires 0 <= col && col < cols;
      @   ensures \result == pieces[row][col];
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ /*@ nullable @*/ Piece piece(int row, int col) {
        if (!positionExists(row, col)) {
            throw new BoardException("A posição solicitada não existe.");
        }

        return pieces[row][col];
    }

    /*@ public normal_behavior
      @   requires pos != null;
      @   requires positionExists(pos);
      @   ensures \result == pieces[pos.getRow()][pos.getCol()];
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ /*@ nullable @*/ Piece piece(Position pos) {
        if (!positionExists(pos)) {
            throw new BoardException("A posição solicitada não existe.");
        }

        return pieces[pos.getRow()][pos.getCol()];
    }

    /*@ public normal_behavior
      @   requires piece != null;
      @   requires pos != null;
      @   requires positionExists(pos);
      @   requires !isPiecePlaced(pos);
      @   requires \typeof(pieces) == \type(Piece[][]);
      @   assignable pieces[pos.getRow()][pos.getCol()], piece.position;
      @   ensures pieces[pos.getRow()][pos.getCol()] == piece;
      @   ensures piece.position == pos;
      @*/
    public void placePiece(Piece piece, Position pos) {
        if (isPiecePlaced(pos)) {
            throw new BoardException("Uma peça já ocupa a posição " + pos);
        }

        pieces[pos.getRow()][pos.getCol()] = piece;
        piece.position = pos;
    }

    /*@ public normal_behavior
      @   requires pos != null;
      @   requires positionExists(pos);
      @*/
    public /*@ nullable @*/ Piece removePiece(Position pos) {
        if (!positionExists(pos)) {
            throw new BoardException("A posição solicitada não existe.");
        }

        if (piece(pos) == null) {
            return null;
        }
        Piece aux = piece(pos);
        aux.position = null;

        pieces[pos.getRow()][pos.getCol()] = null;
        return aux;
    }

    /*@ private normal_behavior
      @   ensures \result <==> (row >= 0 && row < rows && col >= 0 && col < cols);
      @   assignable \nothing;
      @*/
    private /*@ pure @*/ boolean positionExists(int row, int col) {
        return row >= 0 && row < rows && col >= 0 && col < cols;
    }

    /*@ public normal_behavior
      @   requires pos != null;
      @   ensures \result <==>
      @           (pos.getRow() >= 0 && pos.getRow() < rows
      @         && pos.getCol() >= 0 && pos.getCol() < cols);
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ boolean positionExists(Position pos) {
        return positionExists(pos.getRow(), pos.getCol());
    }

    /*@ public normal_behavior
      @   requires pos != null;
      @   requires positionExists(pos);
      @   ensures \result <==> (pieces[pos.getRow()][pos.getCol()] != null);
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ boolean isPiecePlaced(Position pos) {
        if (!positionExists(pos)) {
            throw new BoardException("A posição solicitada não existe.");
        }

        return pieces[pos.getRow()][pos.getCol()] != null;
    }
}
