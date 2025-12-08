package chess.pieces;

import boardgame.Board;
import boardgame.Position;
import chess.ChessPiece;
import chess.Color;

public class Queen extends ChessPiece {

    /*@ public normal_behavior
      @   requires board != null;
      @   requires color != null;
      @   ensures getColor() == color;
      @   ensures getMoveCount() == 0;
      @   ensures getBoard() == board;
      @*/
    public Queen(/*@ non_null @*/ Board board, /*@ non_null @*/ Color color) {
        super(board, color);
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
      @   // A posição atual da rainha não é um movimento válido
      @   ensures !\result[position.getRow()][position.getCol()];
      @
      @   // Movimentos apenas em linha reta (horizontal, vertical ou diagonal)
      @   ensures (\forall int r, c;
      @               0 <= r && r < 8 && 0 <= c && c < 8 && \result[r][c];
      @               r == position.getRow() ||                           // horizontal
      @               c == position.getCol() ||                           // vertical
      @               java.lang.Math.abs(r - position.getRow())
      @                   == java.lang.Math.abs(c - position.getCol())); // diagonal
      @
      @   assignable \nothing;
      @*/
    @Override
    public boolean[][] possibleMoves() {
        boolean[][] mat = new boolean[getBoard().getRows()][getBoard().getCols()];

        Position p = new Position(0, 0);

        // ========================================
        // MOVIMENTOS ORTOGONAIS (como Torre)
        // ========================================

        // Para cima (Norte)
        p.setValues(position.getRow() - 1, position.getCol());
        /*@ loop_invariant p.getRow() >= -1;
          @ loop_invariant (\forall int r; 0 <= r && r < 8 && mat[r][position.getCol()] &&
          @                     r < position.getRow(); true);
          @ decreases p.getRow() + 1;
          @*/
        while (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
            mat[p.getRow()][p.getCol()] = true;
            p.setRow(p.getRow() - 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Para esquerda (Oeste)
        p.setValues(position.getRow(), position.getCol() - 1);
        /*@ loop_invariant p.getCol() >= -1;
          @ decreases p.getCol() + 1;
          @*/
        while (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
            mat[p.getRow()][p.getCol()] = true;
            p.setCol(p.getCol() - 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Para direita (Leste)
        p.setValues(position.getRow(), position.getCol() + 1);
        /*@ loop_invariant p.getCol() <= 8;
          @ decreases 8 - p.getCol();
          @*/
        while (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
            mat[p.getRow()][p.getCol()] = true;
            p.setCol(p.getCol() + 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Para baixo (Sul)
        p.setValues(position.getRow() + 1, position.getCol());
        /*@ loop_invariant p.getRow() <= 8;
          @ decreases 8 - p.getRow();
          @*/
        while (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
            mat[p.getRow()][p.getCol()] = true;
            p.setRow(p.getRow() + 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // ========================================
        // MOVIMENTOS DIAGONAIS (como Bispo)
        // ========================================

        // Noroeste (NW)
        p.setValues(position.getRow() - 1, position.getCol() - 1);
        /*@ loop_invariant p.getRow() >= -1 && p.getCol() >= -1;
          @ decreases p.getRow() + p.getCol() + 2;
          @*/
        while (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
            mat[p.getRow()][p.getCol()] = true;
            p.setValues(p.getRow() - 1, p.getCol() - 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Nordeste (NE)
        p.setValues(position.getRow() - 1, position.getCol() + 1);
        /*@ loop_invariant p.getRow() >= -1 && p.getCol() <= 8;
          @ decreases p.getRow() + (8 - p.getCol()) + 2;
          @*/
        while (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
            mat[p.getRow()][p.getCol()] = true;
            p.setValues(p.getRow() - 1, p.getCol() + 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Sudeste (SE)
        p.setValues(position.getRow() + 1, position.getCol() + 1);
        /*@ loop_invariant p.getRow() <= 8 && p.getCol() <= 8;
          @ decreases (8 - p.getRow()) + (8 - p.getCol()) + 2;
          @*/
        while (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
            mat[p.getRow()][p.getCol()] = true;
            p.setValues(p.getRow() + 1, p.getCol() + 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Sudoeste (SW)
        p.setValues(position.getRow() + 1, position.getCol() - 1);
        /*@ loop_invariant p.getRow() <= 8 && p.getCol() >= -1;
          @ decreases (8 - p.getRow()) + p.getCol() + 2;
          @*/
        while (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
            mat[p.getRow()][p.getCol()] = true;
            p.setValues(p.getRow() + 1, p.getCol() - 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        return mat;
    }

    /*@ also
      @ public normal_behavior
      @   ensures \result != null;
      @   ensures \result.equals("Q");
      @   assignable \nothing;
      @*/
    @Override
    public /*@ pure non_null @*/ String toString() {
        return "Q";
    }
}
