package chess.pieces;

import boardgame.Board;
import boardgame.Position;
import chess.ChessMatch;
import chess.ChessPiece;
import chess.Color;

/**
 * Classe que representa um Peão no jogo de xadrez.
 */
public class Pawn extends ChessPiece {

    //@ public invariant match != null;

    //@ spec_public
    private final /*@ non_null @*/ ChessMatch match;

    /*@ public normal_behavior
      @   requires board != null;
      @   requires color != null;
      @   requires match != null;
      @   ensures getColor() == color;
      @   ensures getMoveCount() == 0;
      @   ensures getBoard() == board;
      @   ensures this.match == match;
      @*/
    public Pawn(/*@ non_null @*/ Board board,
            /*@ non_null @*/ Color color,
            /*@ non_null @*/ ChessMatch match) {
        super(board, color);
        this.match = match;
    }

    /*@ also
      @ public normal_behavior
      @   requires position != null;
      @   requires position.getRow() >= 0 && position.getRow() < 8;
      @   requires position.getCol() >= 0 && position.getCol() < 8;
      @   requires getBoard() != null;
      @   requires getBoard().getRows() == 8;
      @   requires getBoard().getCols() == 8;
      @   requires match != null;
      @
      @   ensures \result != null;
      @   ensures \result.length == 8;
      @   ensures (\forall int i; 0 <= i && i < 8;
      @               \result[i] != null && \result[i].length == 8);
      @
      @   // A posição atual do peão não é um movimento válido
      @   ensures !\result[position.getRow()][position.getCol()];
      @
      @   // Peões brancos só se movem para cima (row decresce)
      @   ensures getColor() == Color.WHITE ==>
      @           (\forall int r, c; 0 <= r && r < 8 && 0 <= c && c < 8 && \result[r][c];
      @               r < position.getRow());
      @
      @   // Peões pretos só se movem para baixo (row aumenta)
      @   ensures getColor() == Color.BLACK ==>
      @           (\forall int r, c; 0 <= r && r < 8 && 0 <= c && c < 8 && \result[r][c];
      @               r > position.getRow());
      @
      @   // Movimento máximo é de 2 casas (primeiro movimento) ou 1 casa (demais)
      @   ensures getColor() == Color.WHITE ==>
      @           (\forall int r, c; 0 <= r && r < 8 && 0 <= c && c < 8 && \result[r][c];
      @               position.getRow() - r <= 2 &&
      @               position.getRow() - r >= 1);
      @
      @   ensures getColor() == Color.BLACK ==>
      @           (\forall int r, c; 0 <= r && r < 8 && 0 <= c && c < 8 && \result[r][c];
      @               r - position.getRow() <= 2 &&
      @               r - position.getRow() >= 1);
      @
      @   // Movimento de 2 casas somente se ainda não moveu
      @   ensures getMoveCount() > 0 ==>
      @           (\forall int r, c; 0 <= r && r < 8 && 0 <= c && c < 8 && \result[r][c];
      @               java.lang.Math.abs(r - position.getRow()) == 1);
      @
      @   assignable \nothing;
      @*/
    @Override
    public boolean[][] possibleMoves() {
        boolean[][] mat = new boolean[getBoard().getRows()][getBoard().getCols()];
        Position p = new Position(0, 0);

        if (getColor() == Color.WHITE) {
            // Um para frente (brancas sobem - row decresce)
            p.setValues(position.getRow() - 1, position.getCol());
            if (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
                mat[p.getRow()][p.getCol()] = true;

                // Dois para frente (primeiro movimento)
                p.setValues(position.getRow() - 2, position.getCol());
                if (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p) && getMoveCount() == 0) {
                    mat[p.getRow()][p.getCol()] = true;
                }
            }

            // Captura diagonal esquerda
            p.setValues(position.getRow() - 1, position.getCol() - 1);
            if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
                mat[p.getRow()][p.getCol()] = true;
            }

            // Captura diagonal direita
            p.setValues(position.getRow() - 1, position.getCol() + 1);
            if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
                mat[p.getRow()][p.getCol()] = true;
            }

            // En Passant (brancas)
            if (position.getRow() == 3) {
                Position left = new Position(position.getRow(), position.getCol() - 1);
                if (getBoard().positionExists(left)
                        && isThereOpponentPiece(left)
                        && getBoard().piece(left) == match.getEnPassantVulnerable()) {
                    mat[left.getRow() - 1][left.getCol()] = true;
                }
                Position right = new Position(position.getRow(), position.getCol() + 1);
                if (getBoard().positionExists(right)
                        && isThereOpponentPiece(right)
                        && getBoard().piece(right) == match.getEnPassantVulnerable()) {
                    mat[right.getRow() - 1][right.getCol()] = true;
                }
            }
        } else {
            // Um para frente (pretas descem - row aumenta)
            p.setValues(position.getRow() + 1, position.getCol());
            if (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p)) {
                mat[p.getRow()][p.getCol()] = true;

                // Dois para frente (primeiro movimento)
                p.setValues(position.getRow() + 2, position.getCol());
                if (getBoard().positionExists(p) && !getBoard().isPiecePlaced(p) && getMoveCount() == 0) {
                    mat[p.getRow()][p.getCol()] = true;
                }
            }

            // Captura diagonal esquerda (pretas)
            p.setValues(position.getRow() + 1, position.getCol() - 1);
            if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
                mat[p.getRow()][p.getCol()] = true;
            }

            // Captura diagonal direita (pretas)
            p.setValues(position.getRow() + 1, position.getCol() + 1);
            if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
                mat[p.getRow()][p.getCol()] = true;
            }

            // En Passant (pretas)
            if (position.getRow() == 4) {
                Position left = new Position(position.getRow(), position.getCol() - 1);
                if (getBoard().positionExists(left)
                        && isThereOpponentPiece(left)
                        && getBoard().piece(left) == match.getEnPassantVulnerable()) {
                    mat[left.getRow() + 1][left.getCol()] = true;
                }
                Position right = new Position(position.getRow(), position.getCol() + 1);
                if (getBoard().positionExists(right)
                        && isThereOpponentPiece(right)
                        && getBoard().piece(right) == match.getEnPassantVulnerable()) {
                    mat[right.getRow() + 1][right.getCol()] = true;
                }
            }
        }

        return mat;
    }

    /*@ also
      @ public normal_behavior
      @   ensures \result != null;
      @   ensures \result.equals("P");
      @   assignable \nothing;
      @*/
    @Override
    public /*@ pure non_null @*/ String toString() {
        return "P";
    }
}
