/**
 * The extension-facing bus contract.
 *
 * These channels are strictly post-commit observations: the board emits them
 * after a transition has been applied and the invariant re-checked, and no
 * delivery guarantee depends on a subscriber hearing one. `pi.events` is a
 * per-process `EventEmitter`, so these reach extensions in this process only;
 * the file remains the inter-process channel.
 */

export const BOARD_CHANGED = "board:changed";
export const BOARD_DELIVERED = "board:delivered";
export const BOARD_POST = "board:post";
export const BOARD_FAILED = "board:failed";

/** The board moved: a local mutation, or a refresh that saw another process's. */
export interface BoardChangedEvent {
  readonly revision: number;
  readonly origin: "local" | "observed";
}

/** One direct message was injected into this session's context. */
export interface BoardDeliveredEvent {
  readonly box: string;
  readonly message: string;
  readonly from: string | null;
}

/** One forum post was appended to the log. */
export interface BoardPostEvent {
  readonly topic: string;
  readonly post: string;
  readonly author: string | null;
}

/** One direct message was settled as failed. */
export interface BoardFailedEvent {
  readonly box: string;
  readonly message: string;
  readonly reason: string | null;
}
