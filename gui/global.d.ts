import { Buffer } from 'buffer'

declare global {
  interface Window {
    Buffer: typeof Buffer
  }
}