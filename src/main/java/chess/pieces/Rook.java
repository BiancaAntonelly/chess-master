package chess.pieces;

import boardgame.Board;
import boardgame.Position;
import chess.ChessPiece;
import chess.Color;

public class Rook extends ChessPiece {

    /*@ public normal_behavior
      @   requires board != null;
      @   requires color != null;
      @*/
    public Rook(Board board, Color color) {
        super(board, color);
    }

    /*@ also
      @ public normal_behavior
      @   ensures \result != null;
      @   ensures \result.equals("R");
      @   assignable \nothing;
      @   pure
      @*/
    @Override
    public String toString() {
        return "R";
    }

    /*@ also
      @ public normal_behavior
      @   requires position != null;
      @   requires 0 <= position.getRow() && position.getRow() < 8;
      @   requires 0 <= position.getCol() && position.getCol() < 8;
      @
      @   ensures \result != null;
      @   ensures \result.length == 8;
      @   ensures (\forall int i; 0 <= i && i < 8;
      @               \result[i] != null && \result[i].length == 8);
      @
      @   // --- Direção para CIMA ---
      @   ensures (\forall int r, c;
      @               \result[r][c] && r < position.getRow()
      @               ==> c == position.getCol());
      @
      @   // --- Direção para BAIXO ---
      @   ensures (\forall int r, c;
      @               \result[r][c] && r > position.getRow()
      @               ==> c == position.getCol());
      @
      @   // --- Direção para ESQUERDA ---
      @   ensures (\forall int r, c;
      @               \result[r][c] && c < position.getCol()
      @               ==> r == position.getRow());
      @
      @   // --- Direção para DIREITA ---
      @   ensures (\forall int r, c;
      @               \result[r][c] && c > position.getCol()
      @               ==> r == position.getRow());
      @
      @   ensures !\result[position.getRow()][position.getCol()];
      @
      @   assignable \nothing;
      @*/
    @Override
    public boolean[][] possibleMoves() {

        boolean[][] mat = new boolean[getBoard().getRows()][getBoard().getCols()];
        Position p = new Position(0, 0);

        // ============================
        // PARA CIMA
        // ============================
        p.setValues(position.getRow() - 1, position.getCol());

        /*@ loop_invariant getBoard().positionExists(p) ==> p.getCol() == position.getCol();
          @ loop_invariant p.getRow() <= position.getRow() - 1;
          @ loop_invariant (\forall int rr, cc;
          @        rr <= position.getRow() - 1 && rr > p.getRow() && cc == position.getCol();
          @        mat[rr][cc] == true);
          @ decreases p.getRow();
         @*/
        while (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
            mat[p.getRow()][p.getCol()] = true;
            p.setRow(p.getRow() - 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }


        // ============================
        // PARA ESQUERDA
        // ============================
        p.setValues(position.getRow(), position.getCol() - 1);

        /*@ loop_invariant getBoard().positionExists(p) ==> p.getRow() == position.getRow();
          @ loop_invariant p.getCol() <= position.getCol() - 1;
          @ loop_invariant (\forall int rr, cc;
          @        rr == position.getRow() && cc < position.getCol() && cc > p.getCol();
          @        mat[rr][cc] == true);
          @ decreases p.getCol();
         @*/
        while (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
            mat[p.getRow()][p.getCol()] = true;
            p.setCol(p.getCol() - 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }


        // ============================
        // PARA DIREITA
        // ============================
        p.setValues(position.getRow(), position.getCol() + 1);

        /*@ loop_invariant getBoard().positionExists(p) ==> p.getRow() == position.getRow();
          @ loop_invariant p.getCol() >= position.getCol() + 1;
          @ loop_invariant (\forall int rr, cc;
          @        rr == position.getRow() && cc > position.getCol() && cc < p.getCol();
          @        mat[rr][cc] == true);
          @ decreases (8 - p.getCol());
         @*/
        while (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
            mat[p.getRow()][p.getCol()] = true;
            p.setCol(p.getCol() + 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }


        // ============================
        // PARA BAIXO
        // ============================
        p.setValues(position.getRow() + 1, position.getCol());

        /*@ loop_invariant getBoard().positionExists(p) ==> p.getCol() == position.getCol();
          @ loop_invariant p.getRow() >= position.getRow() + 1;
          @ loop_invariant (\forall int rr, cc;
          @        rr > position.getRow() && rr < p.getRow() && cc == position.getCol();
          @        mat[rr][cc] == true);
          @ decreases (8 - p.getRow());
         @*/
        while (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
            mat[p.getRow()][p.getCol()] = true;
            p.setRow(p.getRow() + 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        return mat;
    }
}
