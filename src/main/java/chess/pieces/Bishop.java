package chess.pieces;

import boardgame.Board;
import boardgame.Position;
import chess.ChessPiece;
import chess.Color;

/**
 * Classe que representa um Bispo no jogo de xadrez.
 * O bispo move-se diagonalmente em qualquer direção,
 * quantas casas quiser, desde que não haja peças bloqueando.
 */
public class Bishop extends ChessPiece {

    /*@ public normal_behavior
      @   requires board != null;
      @   requires color != null;
      @   ensures getColor() == color;
      @   ensures getMoveCount() == 0;
      @   ensures getBoard() == board;
      @*/
    public Bishop(/*@ non_null @*/ Board board, /*@ non_null @*/ Color color) {
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
      @   // A posição atual do bispo não é um movimento válido
      @   ensures !\result[position.getRow()][position.getCol()];
      @
      @   // Movimentos apenas em diagonais (diferença absoluta de linhas == diferença absoluta de colunas)
      @   ensures (\forall int r, c;
      @               0 <= r && r < 8 && 0 <= c && c < 8 && \result[r][c];
      @               java.lang.Math.abs(r - position.getRow()) ==
      @               java.lang.Math.abs(c - position.getCol()));
      @
      @   assignable \nothing;
      @*/
    @Override
    public boolean[][] possibleMoves() {
        boolean[][] mat = new boolean[getBoard().getRows()][getBoard().getCols()];

        Position p = new Position(0, 0);

        // Noroeste (NW) - diagonal superior esquerda
        p.setValues(position.getRow() - 1, position.getCol() - 1);

        /*@ loop_invariant p.getRow() >= -1 && p.getCol() >= -1;
          @ loop_invariant (\forall int r, c;
          @                     0 <= r && r < 8 && 0 <= c && c < 8 && mat[r][c] &&
          @                     r < position.getRow() && c < position.getCol();
          @                     r - position.getRow() == c - position.getCol());
          @ decreases p.getRow() + p.getCol() + 2;
          @*/
        while (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
            mat[p.getRow()][p.getCol()] = true;
            p.setValues(p.getRow() - 1, p.getCol() - 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Nordeste (NE) - diagonal superior direita
        p.setValues(position.getRow() - 1, position.getCol() + 1);

        /*@ loop_invariant p.getRow() >= -1 && p.getCol() <= 8;
          @ loop_invariant (\forall int r, c;
          @                     0 <= r && r < 8 && 0 <= c && c < 8 && mat[r][c] &&
          @                     r < position.getRow() && c > position.getCol();
          @                     position.getRow() - r == c - position.getCol());
          @ decreases p.getRow() + (8 - p.getCol()) + 2;
          @*/
        while (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
            mat[p.getRow()][p.getCol()] = true;
            p.setValues(p.getRow() - 1, p.getCol() + 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Sudeste (SE) - diagonal inferior direita
        p.setValues(position.getRow() + 1, position.getCol() + 1);

        /*@ loop_invariant p.getRow() <= 8 && p.getCol() <= 8;
          @ loop_invariant (\forall int r, c;
          @                     0 <= r && r < 8 && 0 <= c && c < 8 && mat[r][c] &&
          @                     r > position.getRow() && c > position.getCol();
          @                     r - position.getRow() == c - position.getCol());
          @ decreases (8 - p.getRow()) + (8 - p.getCol()) + 2;
          @*/
        while (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
            mat[p.getRow()][p.getCol()] = true;
            p.setValues(p.getRow() + 1, p.getCol() + 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Sudoeste (SW) - diagonal inferior esquerda
        p.setValues(position.getRow() + 1, position.getCol() - 1);

        /*@ loop_invariant p.getRow() <= 8 && p.getCol() >= -1;
          @ loop_invariant (\forall int r, c;
          @                     0 <= r && r < 8 && 0 <= c && c < 8 && mat[r][c] &&
          @                     r > position.getRow() && c < position.getCol();
          @                     r - position.getRow() == position.getCol() - c);
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
      @   ensures \result.equals("B");
      @   assignable \nothing;
      @*/
    @Override
    public /*@ pure non_null @*/ String toString() {
        return "B";
    }
}
