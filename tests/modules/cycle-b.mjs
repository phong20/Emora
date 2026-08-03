import { a } from "./cycle-a.mjs";
export function b() {
  a();
}
