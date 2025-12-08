package chess.pieces;

import boardgame.Board;
import boardgame.Position;
import chess.ChessPiece;
import chess.Color;

/**
 * Classe que representa uma Torre no jogo de xadrez.
 */
public class Rook extends ChessPiece {

    /*@ public normal_behavior
      @   requires board != null;
      @   requires color != null;
      @   ensures getColor() == color;
      @   ensures getMoveCount() == 0;
      @   ensures getBoard() == board;
      @*/
    public Rook(/*@ non_null @*/ Board board, /*@ non_null @*/ Color color) {
        super(board, color);
    }

    /*@ also
      @ public normal_behavior
      @   ensures \result != null;
      @   ensures \result.equals("R");
      @   assignable \nothing;
      @*/
    @Override
    public /*@ pure non_null @*/ String toString() {
        return "R";
    }

    /*@ also
      @ public normal_behavior
      @   requires position != null;
      @   requires position.getRow() >= 0 && position.getRow() < 8;
      @   requires position.getCol() >= 0 && position.getCol() < 8;
      @   requires getBoard() != null;
      @   requires getBoard().getRows() == 8;
      @   requires getBoard().getCols() == 8;
      @
      @   ensures \result != null;
      @   ensures \result.length == 8;
      @   ensures (\forall int i; 0 <= i && i < 8;
      @               \result[i] != null && \result[i].length == 8);
      @
      @   ensures !\result[position.getRow()][position.getCol()];
      @
      @   ensures (\forall int r, c;
      @               0 <= r && r < 8 && 0 <= c && c < 8 && \result[r][c];
      @               r == position.getRow() || c == position.getCol());
      @
      @   assignable \nothing;
      @*/
    @Override
    public boolean[][] possibleMoves() {

        boolean[][] mat = new boolean[getBoard().getRows()][getBoard().getCols()];
        Position p = new Position(0, 0);

        // PARA CIMA
        if (position.getRow() > 0) {
            p.setValues(position.getRow() - 1, position.getCol());

            /*@ loop_invariant p.getRow() >= -1;
              @ loop_invariant p.getCol() == position.getCol();
              @ loop_invariant (\forall int r; 0 <= r && r < 8;
              @                     mat[r][position.getCol()] ==> r < position.getRow());
              @ decreases p.getRow() + 1;
              @*/
            while (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
                mat[p.getRow()][p.getCol()] = true;
                if (p.getRow() == 0) break;
                p.setRow(p.getRow() - 1);
            }
            if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
                mat[p.getRow()][p.getCol()] = true;
            }
        }

        // PARA ESQUERDA
        if (position.getCol() > 0) {
            p.setValues(position.getRow(), position.getCol() - 1);

            /*@ loop_invariant p.getCol() >= -1;
              @ loop_invariant p.getRow() == position.getRow();
              @ loop_invariant (\forall int c; 0 <= c && c < 8;
              @                     mat[position.getRow()][c] ==> c < position.getCol());
              @ decreases p.getCol() + 1;
              @*/
            while (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
                mat[p.getRow()][p.getCol()] = true;
                if (p.getCol() == 0) break;
                p.setCol(p.getCol() - 1);
            }
            if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
                mat[p.getRow()][p.getCol()] = true;
            }
        }

        // PARA DIREITA
        if (position.getCol() < 7) {
            p.setValues(position.getRow(), position.getCol() + 1);

            /*@ loop_invariant p.getCol() <= 8;
              @ loop_invariant p.getRow() == position.getRow();
              @ loop_invariant (\forall int c; 0 <= c && c < 8;
              @                     mat[position.getRow()][c] ==> c > position.getCol());
              @ decreases 8 - p.getCol();
              @*/
            while (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
                mat[p.getRow()][p.getCol()] = true;
                if (p.getCol() == 7) break;
                p.setCol(p.getCol() + 1);
            }
            if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
                mat[p.getRow()][p.getCol()] = true;
            }
        }

        // PARA BAIXO
        if (position.getRow() < 7) {
            p.setValues(position.getRow() + 1, position.getCol());

            /*@ loop_invariant p.getRow() <= 8;
              @ loop_invariant p.getCol() == position.getCol();
              @ loop_invariant (\forall int r; 0 <= r && r < 8;
              @                     mat[r][position.getCol()] ==> r > position.getRow());
              @ decreases 8 - p.getRow();
              @*/
            while (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
                mat[p.getRow()][p.getCol()] = true;
                if (p.getRow() == 7) break;
                p.setRow(p.getRow() + 1);
            }
            if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
                mat[p.getRow()][p.getCol()] = true;
            }
        }

        return mat;
    }
}
