import { b } from "./cycle-b.mjs";
export function a() {
  b();
}
