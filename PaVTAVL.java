package trees.pavt;

import java.util.Comparator;

/**
 * Implementation of concurrent AVL tree based on the paper 
 * "Practical Concurrent Traversals in Search Trees" by 
 * Dana Drachsler-Cohen (ETH), Martin Vechev (ETH) and Eran Yahav (Technion).
 *
 * Copyright 2013 Dana Drachsler-Cohen (ddana [at] inf [dot] ethz [dot] ch).
 * 
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it wfill be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * @author Dana Drachsler-Cohen
 */
public class PaVTAVL <K,V> {

	protected PaVTAVLNode<K, V> root;
	protected PaVTAVLNode<K, V> rightSentinel;
	protected PaVTAVLNode<K, V> leftSentinel;
	private Comparator<? super K> comparator;


	public PaVTAVL(K min, K max) {
		rightSentinel = new PaVTAVLNode<K, V>(min);
		leftSentinel = new PaVTAVLNode<K, V>(max);
		leftSentinel.parent = rightSentinel;
		rightSentinel.right = leftSentinel;
		leftSentinel.leftSnapshot = rightSentinel;
		root = leftSentinel;
	}

	@SuppressWarnings("unchecked")
	private Comparable<? super K> comparable(final Object key) {
		if (key == null) {
			throw new NullPointerException();
		}
		if (comparator == null) {
			return (Comparable<? super K>)key;
		}
		return new Comparable<K>() {
			final Comparator<? super K> _cmp = comparator;

			@SuppressWarnings("unchecked")
			public int compareTo(final K rhs) { return _cmp.compare((K)key, rhs); }
		};
	}

	public V add(final K val, final V item) {
		final Comparable<? super K> value = comparable(val);
		while (true) {
			PaVTAVLNode<K, V> node = root;
			PaVTAVLNode<K,V> child;
			int res = -1;
			while (true) {
				if (res == 0) break;
				if (res < 0) {
					child = node.left;
				} else {
					child = node.right;
				}
				if (child == null) {
					break;
				}
				node = child;
				K v = node.value;
				res = value.compareTo(v);
			}
			if (res == 0) {
				V item2 = (V) node.item;
				return item2;
			}
			boolean leftLast = res < 0;
			synchronized (node) {
				if (node.marked || (leftLast && node.left != null) || (!leftLast && node.right != null)) {
					continue;
				}
				PaVTAVLNode<K, V> upperNode = leftLast? node.leftSnapshot : node.rightSnapshot;
				if ((leftLast && (value.compareTo(upperNode.value) <= 0)) || 
						(!leftLast && (value.compareTo(upperNode.value) >= 0)
								)) {
					continue;
				}
				PaVTAVLNode<K, V> newNode = new PaVTAVLNode<K, V>(val, item);
				newNode.parent = node;
				newNode.height = 1;
				if (res > 0) {
					newNode.rightSnapshot = upperNode;
					newNode.leftSnapshot = node;
					upperNode.leftSnapshot = newNode;
					node.rightSnapshot = newNode;
					node.right = newNode;
				} else { 
					newNode.leftSnapshot = upperNode;
					newNode.rightSnapshot = node;
					upperNode.rightSnapshot = newNode;
					node.leftSnapshot = newNode;
					node.left = newNode;
				}
				if (node == root) {
					return null;
				}
			}
			rebalanceSynchronized(node);
			return null;
		}
	}

	public V remove(K val) {
		final Comparable<? super K> value = comparable(val);
		while (true) {
			PaVTAVLNode<K, V> leftNode = leftSentinel;
			PaVTAVLNode<K, V> rightNode = rightSentinel;
			PaVTAVLNode<K, V> node = root;
			PaVTAVLNode<K,V> child;
			int res = -1;
			while (true) {
				if (res == 0) break;
				if (res < 0) {
					leftNode = node;
					child = node.left;
				} else {
					rightNode = node;
					child = node.right;
				}
				if (child == null) {
					break;
				}
				node = child;
				K v = node.value;
				res = value.compareTo(v);
			}
			if (res != 0) {
				boolean leftLast = res < 0;
				PaVTAVLNode<K, V> ref = leftLast? leftNode.leftSnapshot : rightNode.rightSnapshot;
				if ((leftLast && (value.compareTo(ref.value) <= 0)) || 
						(!leftLast && (value.compareTo(ref.value) >=0))) {
					continue;
				}
				return null;
			}
			PaVTAVLNode<K, V> parent = node.parent;
			PaVTAVLNode<K, V> toRebalance = null;
			PaVTAVLNode<K, V> toRebalance2 = null;
			synchronized(parent) {
				if (node.parent != parent) {
					if (node.marked) return null;
					continue;
				}
				synchronized(node) {
					if (node.marked) {
						return null;
					}
					PaVTAVLNode<K, V> left = node.left;
					PaVTAVLNode<K, V> right = node.right;
					boolean leftChild = parent.left == node;
					if (left == null && right == null) {
						rightNode = node.leftSnapshot;
						leftNode = node.rightSnapshot;
						node.marked = true;
						if (leftChild) {
							parent.left = null;
							parent.leftSnapshot = rightNode;
							rightNode.rightSnapshot = parent;
						} else {
							parent.right = null;
							parent.rightSnapshot = leftNode;
							leftNode.leftSnapshot = parent;
						}
						toRebalance = parent;
					} else if (left == null || right == null) {
						child = left == null? right : left;
						rightNode = node.leftSnapshot;
						leftNode = node.rightSnapshot;
						synchronized(child) {
							PaVTAVLNode<K, V> snapshotToLock = left == null? leftNode : rightNode;
							synchronized(snapshotToLock) {
								if ((left == null && snapshotToLock.leftSnapshot != node) ||
										(left != null && snapshotToLock.rightSnapshot != node) || 
										snapshotToLock.marked) {
									continue;
								}
								node.marked = true;
								child = left == null? right : left;
								if (leftChild) {
									parent.left = child;
								} else {
									parent.right = child;
								}
								child.parent = parent;
								rightNode.rightSnapshot = leftNode;
								leftNode.leftSnapshot = rightNode;
								toRebalance = parent;
							}
						}
					} else {
						synchronized(left) {
							synchronized(right) {
								rightNode = node.leftSnapshot;
								leftNode = node.rightSnapshot;
								synchronized(rightNode) {
									if (rightNode.rightSnapshot != node || rightNode.marked) continue;
									if (right.left == null) {
										node.marked = true;
										right.left = left;
										left.parent = right;
										right.parent = parent;
										if (leftChild) {
											parent.left = right;
										} else {
											parent.right = right;
										}
										rightNode.rightSnapshot = leftNode;
										leftNode.leftSnapshot = rightNode;
										toRebalance = right;
									} else {
										PaVTAVLNode<K, V> succ = leftNode;
										PaVTAVLNode<K, V> succParent = succ.parent;
										toRebalance = succParent;
										toRebalance2 = succ;
										synchronized(succParent) {
											if (leftNode.parent != succParent || leftNode.marked) continue;
											synchronized(leftNode) {
												if (leftNode.leftSnapshot != node || leftNode.marked) continue;
												PaVTAVLNode<K, V> succRight = succ.right;
												if (succRight != null) {
													synchronized(succRight) {
														PaVTAVLNode<K, V> succRightSnapshot = succ.rightSnapshot;
														if (succRightSnapshot != succRight) {
															synchronized(succRightSnapshot) {
																if (succRightSnapshot.leftSnapshot != succ || succRightSnapshot.marked) {
																	continue;
																}
																applyRemove(rightNode, node, parent, left, right,
																		leftChild, succ, succParent, succRight, succRightSnapshot);
															}
														} else {
															applyRemove(rightNode, node, parent, left, right,
																	leftChild, succ, succParent, succRight, succRightSnapshot);
														}
													}
												} else {
													PaVTAVLNode<K, V> succRightSnapshot = succ.rightSnapshot;
													applyRemove(rightNode, node, parent, left, right,
															leftChild, succ, succParent, succRight, succRightSnapshot);
												}											
											}
										}
									}
								}	
							}
						}
					}
				}
			}
			rebalanceSynchronized(toRebalance); 
			if (toRebalance2 != null) {
				rebalanceSynchronized(toRebalance2);
			}
			return (V) node.item;
		}
	}

	protected void applyRemove(PaVTAVLNode<K, V> rightNode,
			PaVTAVLNode<K, V> node,
			PaVTAVLNode<K, V> parent,
			PaVTAVLNode<K, V> left,
			PaVTAVLNode<K, V> right, boolean leftChild,
			PaVTAVLNode<K, V> succ,
			PaVTAVLNode<K, V> succParent,
			PaVTAVLNode<K, V> succRight,
			PaVTAVLNode<K, V> succRightSnapshot) {
		node.marked = true;
		succ.height = node.height;
		succ.right = right;
		right.parent = succ;
		succ.left = left;
		left.parent = succ;
		succ.parent = parent;
		if (leftChild) {
			parent.left = succ;
		} else {
			parent.right = succ;
		}
		succParent.left = succRight;
		succ.rightSnapshot = succRightSnapshot;
		succRightSnapshot.leftSnapshot = succ;
		if (succRight != null) {
			succRight.parent = succParent;
		} 
		succ.leftSnapshot = rightNode;
		rightNode.rightSnapshot = succ;
	}

	public boolean contains(K val) {
		final Comparable<? super K> value = comparable(val);
		while (true) {
			PaVTAVLNode<K, V> node = root;
			PaVTAVLNode<K,V> child;
			int res = -1;
			while (true) {
				if (res == 0) break;
				if (res < 0) {
					child = node.left;
				} else {
					child = node.right;
				}
				if (child == null) {
					break;
				}
				node = child;
				K v = node.value;
				res = value.compareTo(v);
			}
			if (res == 0) {
				return true;
			}
			PaVTAVLNode<K, V> upperNode = res < 0? node.leftSnapshot: node.rightSnapshot;
			if ((res < 0 && value.compareTo(upperNode.value) <= 0) || (res > 0 && value.compareTo(upperNode.value) >= 0)) {
				continue;
			}

			return false;
		}
	}


	public int size() {
		PaVTAVLNode<K, V> n = root.left;
		return size(n);
	}

	private int size(PaVTAVLNode<K, V> n) {
		if (n == null) return 0;
		return 1 + size(n.left) +  size(n.right);
	}

	public boolean check() {
		PaVTAVLNode<K, V> n = root.parent;
		K max = root.parent.value;
		while (n.rightSnapshot != null) {
			PaVTAVLNode<K, V> next = n.rightSnapshot;
			if (next.leftSnapshot != n) {
				return false;
			}
			if (comparable(max).compareTo(next.value) >= 0) {
				return false;
			}
			max = next.value;
			n = next;
		}
		return true;
	}

	final private void rebalanceSynchronized(PaVTAVLNode<K,V> node) {
		if (node == root) {
			return;
		}
		PaVTAVLNode<K,V> parent = node.parent;
		while (node != root) {
			synchronized (parent) {
				if (node.parent != parent) {
					if (node.marked) return;
					parent = node.parent; continue;
				}
				synchronized(node) {
					if (node.marked) return;
					PaVTAVLNode<K, V> left = node.left;
					PaVTAVLNode<K, V> right = node.right;
					int leftHeight = left == null? 0 : left.height;
					int rightHeight = right == null? 0 : right.height;
					int newHeight = Math.max(leftHeight, rightHeight) + 1;
					int oldHeight = node.height;
					int bf = leftHeight - rightHeight;
					if (newHeight != oldHeight) {
						node.height = newHeight;
					} else if (Math.abs(bf) <= 2) return;

					PaVTAVLNode<K, V> child = bf >= 2? left : bf <= -2? right : null;
					boolean isLeft = bf >= 2;
					if (Math.abs(bf) >= 2) {
						if (child != null) {
							synchronized(child) {
								left = child.left;
								right = child.right;
								leftHeight = left == null? 0 : left.height;
								rightHeight = right == null? 0 : right.height;
								if ((isLeft && (leftHeight - rightHeight) < 0) || (!isLeft && (leftHeight - rightHeight) > 0)) {
									PaVTAVLNode<K,V> grandChild =  isLeft? child.right : child.left;
									synchronized(grandChild) {
										rotate(grandChild, child, node, isLeft);
										rotate(grandChild, node, parent, !isLeft);
									}
									node = grandChild;
								} else {
									rotate(child, node, parent, !isLeft);
									node = child;
								}
							}
						}
					} else {
						node = parent;
						parent = node.parent;
					}
				}
			}
		}
	}


	/**
	 * Apply a single rotation to the given node.
	 * 
	 * @param child The node's child
	 * @param node The node to rotate
	 * @param parent The node's parent
	 * @param left Is this a left rotation?
	 */
	final private void rotate(final PaVTAVLNode<K,V> child, final PaVTAVLNode<K,V> node, final PaVTAVLNode<K,V> parent, boolean left) {
		boolean isLeft = parent.left == node;
		if (isLeft) {
			parent.left = child;
		} else {
			parent.right = child;
		}
		child.parent = parent;
		node.parent = child;
		PaVTAVLNode<K, V> grandChild = left? child.left : child.right;
		if (grandChild != null) {
				if (left) {
					node.right = grandChild;
					grandChild.parent = node; 
					child.left = node;
					PaVTAVLNode<K, V> rightN = node.right;
					PaVTAVLNode<K, V> leftN = node.left;
					node.height = Math.max(rightN == null? 0 : rightN.height, leftN == null? 0 : leftN.height) + 1;
					PaVTAVLNode<K, V> rightC = child.right;
					child.height = Math.max(node.height, rightC == null? 0 : rightC.height) + 1;
				} else {
					node.left = grandChild;
					grandChild.parent = node; 
					child.right = node;
					PaVTAVLNode<K, V> rightN = node.right;
					PaVTAVLNode<K, V> leftN = node.left;
					node.height = Math.max(rightN == null? 0 : rightN.height, leftN == null? 0 : leftN.height) + 1;
					PaVTAVLNode<K, V> leftC = child.left;
					child.height = Math.max(node.height, leftC == null? 0 : leftC.height) + 1;
				}
		} else {
			if (left) {
				node.right = grandChild;
				child.left = node;
				PaVTAVLNode<K, V> rightN = node.right;
				PaVTAVLNode<K, V> leftN = node.left;
				node.height = Math.max(rightN == null? 0 : rightN.height, leftN == null? 0 : leftN.height) + 1;
				PaVTAVLNode<K, V> rightC = child.right;
				child.height = Math.max(node.height, rightC == null? 0 : rightC.height) + 1;
			} else {
				node.left = grandChild;
				child.right = node;
				PaVTAVLNode<K, V> rightN = node.right;
				PaVTAVLNode<K, V> leftN = node.left;
				node.height = Math.max(rightN == null? 0 : rightN.height, leftN == null? 0 : leftN.height) + 1;
				PaVTAVLNode<K, V> leftC = child.left;
				child.height = Math.max(node.height, leftC == null? 0 : leftC.height) + 1;
			}
		}

	}

	class PaVTAVLNode<K, V> {
		
		public final K value;
		public final Object item;
		public volatile PaVTAVLNode<K, V> leftSnapshot;
		public volatile PaVTAVLNode<K, V> rightSnapshot;
		public int height;
		
		public volatile boolean marked;
		
		public volatile PaVTAVLNode<K, V> parent;
		public volatile PaVTAVLNode<K, V> right;
		public volatile PaVTAVLNode<K, V> left;
		
		public PaVTAVLNode(K value) {
			this(value, null);
		}
		
		public PaVTAVLNode(K value, Object item) {
			this.value = value;
			this.item = item;
			this.marked = false;
		}

		@Override
		public String toString() {
			String delimiter = " ";
			StringBuilder sb = new StringBuilder();
			return sb.append(value + (marked? "(marked)" : "") + delimiter).toString();
		}
		
	}

}

